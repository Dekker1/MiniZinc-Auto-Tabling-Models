/*
 * author: Jean-Noël Monette
 */
include "globals.mzn";

%cubes
set of int: cubes=1..8;

int: ud=0;
int: lr=8;
int: fb=16;

set of int: pos=1..24;
set of int: symbols=0..4*4*4-1;

array[cubes] of var cubes: cube_at;
array[pos] of var symbols: symbol_at;

%Each cube is placed once.
constraint alldifferent(cube_at);

%Party constraints on the 6 faces
constraint party([symbol_at[i] | i in 1..4]);
constraint party([symbol_at[i + 4] | i in 1..4]);
constraint party([symbol_at[(i - 1) * 2 + 1 + lr] | i in 1..4]);
constraint party([symbol_at[i * 2 + lr] | i in 1..4]);
constraint party([symbol_at[if i < 3 then i else i+2 endif + fb] | i in 1..4]);
constraint party([symbol_at[if i < 3 then i else i+2 endif + 2 + fb] | i in 1..4]);

%Linking cubes and symbols
constraint forall(i in {1,4,6,7})(
	   link_cube_and_symbols([cube_at[i],symbol_at[i+ud],symbol_at[i+lr],symbol_at[i+fb]]));
constraint forall(i in {2,3,5,8})(
	   link_cube_and_symbols([cube_at[i],symbol_at[i+ud],symbol_at[i+fb],symbol_at[i+lr]]));

%Sym break
constraint cube_at[1] = 1;
constraint cube_at[2] < cube_at[3];
constraint cube_at[2] < cube_at[5];

%better to search on symbol_at first rather than cube_at
solve :: int_search(symbol_at, first_fail, indomain_min, complete) satisfy;

%introduced because of limitation in output.
array[pos] of var 0..3: color_at = [color(symbol_at[i]) |i in pos];
array[pos] of var 0..3: shape_at = [shape(symbol_at[i]) |i in pos];
array[pos] of var 0..3: fill_at = [fill(symbol_at[i]) |i in pos];
%names (for output)
array[1..4] of string: colorname = ["blue","red","yellow","black"];
array[1..4] of string: fillname = ["half","plain","empty","grid"];
array[1..4] of string: shapename = ["triangle","circle","square","heart"];
output [show(cube_at), "\n", show(symbol_at), "\n"] ++
       ["pos " ++ show(i) ++ ": cube " ++ show(cube_at[i]) ++ "\n"
       ++ "u/d:\t"++fillname[fix(fill_at[i+ud])+1]++"\t"++colorname[fix(color_at[i+ud])+1]++"\t"++shapename[fix(shape_at[i+ud])+1]++"\n"
       ++ "f/b:\t"++fillname[fix(fill_at[i+fb])+1]++"\t"++colorname[fix(color_at[i+fb])+1]++"\t"++shapename[fix(shape_at[i+fb])+1]++"\n"
       ++ "l/r:\t"++fillname[fix(fill_at[i+lr])+1]++"\t"++colorname[fix(color_at[i+lr])+1]++"\t"++shapename[fix(shape_at[i+lr])+1]++"\n"
       | i in 1..8];%fill

predicate diff_or_equal(array[1..4] of var 0..3: x)
=
	  forall(i in 1..4,j in i+1..4)(x[i]!=x[j])
	  \/
	  forall(i in 1..4,j in i+1..4)(x[i]=x[j]);


% A party is alldiff or allequal for each of the three characteristics.
predicate party(array[1..4] of var 0..63: symbols)
= (
	  diff_or_equal([color(symbols[i]) | i in 1..4])
	  /\ diff_or_equal([shape(symbols[i]) | i in 1..4])
	  /\ diff_or_equal([fill(symbols[i]) | i in 1..4])
	);


%How to implement linking functions with the advantages of CSE.
function array[1..3] of var 0..3: fcs(var 0..63:symbol) :: promise_total =
	let { var 0..3: color;  var 0..3:shape;var 0..3: fill;
	constraint  symbol = 4*4*fill+4*color+shape; }
	in [fill,color,shape];
function var 0..3: color_help(array[1..3] of var 0..3: fcs) :: promise_total = fcs[2];
function var 0..3: color(var int:symbol) ::promise_total = color_help(fcs(symbol));
function var 0..3: fill_help(array[1..3] of var 0..3: fcs) :: promise_total = fcs[1];
function var 0..3: fill(var int:symbol) ::promise_total = fill_help(fcs(symbol));
function var 0..3: shape_help(array[1..3] of var 0..3: fcs) :: promise_total = fcs[3];
function var 0..3: shape(var int:symbol) ::promise_total = shape_help(fcs(symbol));

%For parameters
function 0..3: shape(int: symbol) = symbol mod 4;
function 0..3: color(int: symbol) = symbol mod 16 div 4;
function 0..3: fill(int:symbol) = symbol div 16;

array[1..8,1..24] of int: data;

%Which symbol positions on a cube are next to each other on the same corner.
%Made by hand, I do not think there is any hope for finding a simple formula that could be used in precomputation :-)
%Actually it might be divided by three and have a disjunction in link_cube_and_symbols
array[1..24,1..3] of int: pp = [|21,12,7
|23,17,11
|24,4,18
|22,8,3
|1,6,16
|2,14,20
|4,18,24
|3,22,8
|7,21,12
|5,10,15
|6,16,1
|8,3,22
|16,1,6
|15,5,10
|13,9,19
|14,20,2
|18,24,4
|20,2,14
|19,13,9
|17,11,23
|12,7,21
|11,23,17
|9,19,13
|10,15,5
|];
%% ---------- DATA ----------
data =[| 63, 11,  0, 62, 39, 55, 15, 60, 19, 29, 45, 46,  9, 44, 21, 41,  7, 56, 26, 18, 34, 38, 52, 23 |
   31,  6, 10, 38, 51, 57, 42, 44, 16, 48, 11,  4, 15, 63, 35,  2, 49, 25,  8, 47, 54, 39, 21,  9 |
   23, 62, 49,  9, 25, 44, 55, 63, 11, 60, 36, 39, 33, 10, 21, 19, 56, 17,  6, 34, 32, 61, 59,  7 |
   49, 25, 57,  6, 42, 13, 41,  5, 36, 16, 28,  7, 50, 27,  2, 20, 10, 38, 35, 26,  0, 55, 43, 32 |
   47, 43, 12, 19, 54, 52, 28, 46, 42, 24, 20, 45,  0, 23, 48, 29,  3, 58, 18, 50, 16, 37,  2, 56 |
   30,  8, 50,  4, 40, 32, 46, 59, 48,  1,  5, 17, 27, 37, 28, 34, 12, 18, 45, 20, 35, 14, 53, 22 |
   43, 51, 54, 59, 17, 24, 37, 61, 60, 58, 14, 40, 29,  8, 36,  1, 31, 13, 62, 22,  3, 30, 33, 53 |
   57, 33, 31,  3, 61,  5, 15, 22, 12, 58,  1,  4, 14, 53, 30, 26, 40, 51, 41, 24, 52, 13, 27, 47 |]
;
% cubes: [4, 7, 6, 8, 5, 2, 3, 1]
% symbols: [28, 62, 45, 15, 47, 51, 11, 23, 43, 60, 48, 52, 29, 48, 6, 56, 10, 29, 27, 4, 52, 35, 33, 62]
% rotations: [22, 19, 19, 9, 5, 10, 23, 3]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 38, 60, 0, 1, 45, 52, 7, 
    1, 19, 26, 9, 1, 44, 18, 11, 1, 34, 46, 15, 1, 11, 44, 18, 1, 26, 9, 19, 1, 
    39, 29, 21, 1, 62, 56, 23, 1, 9, 19, 26, 1, 21, 39, 29, 1, 46, 15, 34, 1, 
    60, 0, 38, 1, 29, 21, 39, 1, 63, 55, 41, 1, 18, 11, 44, 1, 52, 7, 45, 1, 
    15, 34, 46, 1, 7, 45, 52, 1, 41, 63, 55, 1, 23, 62, 56, 1, 0, 38, 60, 1, 
    56, 23, 62, 1, 55, 41, 63, 2, 31, 57, 2, 2, 42, 54, 4, 2, 63, 47, 6, 2, 15, 
    16, 8, 2, 38, 25, 9, 2, 39, 44, 10, 2, 21, 49, 11, 2, 16, 8, 15, 2, 8, 15, 
    16, 2, 49, 11, 21, 2, 9, 38, 25, 2, 57, 2, 31, 2, 51, 48, 35, 2, 25, 9, 38, 
    2, 44, 10, 39, 2, 54, 4, 42, 2, 10, 39, 44, 2, 6, 63, 47, 2, 35, 51, 48, 2, 
    11, 21, 49, 2, 48, 35, 51, 2, 4, 42, 54, 2, 2, 31, 57, 2, 47, 6, 63, 3, 33, 
    11, 6, 3, 9, 17, 7, 3, 17, 7, 9, 3, 34, 62, 10, 3, 6, 33, 11, 3, 7, 9, 17, 
    3, 23, 44, 19, 3, 25, 60, 21, 3, 44, 19, 23, 3, 60, 21, 25, 3, 39, 55, 32, 
    3, 11, 6, 33, 3, 62, 10, 34, 3, 59, 56, 36, 3, 55, 32, 39, 3, 19, 23, 44, 
    3, 61, 63, 49, 3, 32, 39, 55, 3, 36, 59, 56, 3, 56, 36, 59, 3, 21, 25, 60, 
    3, 63, 49, 61, 3, 10, 34, 62, 3, 49, 61, 63, 4, 7, 41, 0, 4, 42, 16, 2, 4, 
    57, 55, 5, 4, 38, 32, 6, 4, 41, 0, 7, 4, 28, 43, 10, 4, 20, 49, 13, 4, 2, 
    42, 16, 4, 49, 13, 20, 4, 27, 26, 25, 4, 25, 27, 26, 4, 26, 25, 27, 4, 43, 
    10, 28, 4, 6, 38, 32, 4, 50, 36, 35, 4, 35, 50, 36, 4, 32, 6, 38, 4, 0, 7, 
    41, 4, 16, 2, 42, 4, 10, 28, 43, 4, 13, 20, 49, 4, 36, 35, 50, 4, 5, 57, 
    55, 4, 55, 5, 57, 5, 42, 18, 0, 5, 3, 20, 2, 5, 20, 2, 3, 5, 37, 46, 12, 5, 
    45, 28, 16, 5, 0, 42, 18, 5, 58, 56, 19, 5, 2, 3, 20, 5, 50, 43, 23, 5, 48, 
    54, 24, 5, 16, 45, 28, 5, 47, 52, 29, 5, 46, 12, 37, 5, 18, 0, 42, 5, 23, 
    50, 43, 5, 28, 16, 45, 5, 12, 37, 46, 5, 52, 29, 47, 5, 54, 24, 48, 5, 43, 
    23, 50, 5, 29, 47, 52, 5, 24, 48, 54, 5, 19, 58, 56, 5, 56, 19, 58, 6, 28, 
    40, 1, 6, 18, 22, 4, 6, 53, 12, 5, 6, 37, 20, 8, 6, 5, 53, 12, 6, 59, 50, 
    14, 6, 46, 35, 17, 6, 22, 4, 18, 6, 8, 37, 20, 6, 4, 18, 22, 6, 48, 45, 27, 
    6, 40, 1, 28, 6, 32, 34, 30, 6, 34, 30, 32, 6, 30, 32, 34, 6, 17, 46, 35, 
    6, 20, 8, 37, 6, 1, 28, 40, 6, 27, 48, 45, 6, 35, 17, 46, 6, 45, 27, 48, 6, 
    14, 59, 50, 6, 12, 5, 53, 6, 50, 14, 59, 7, 43, 24, 1, 7, 40, 37, 3, 7, 22, 
    51, 8, 7, 53, 59, 13, 7, 33, 31, 14, 7, 58, 36, 17, 7, 51, 8, 22, 7, 1, 43, 
    24, 7, 60, 62, 29, 7, 61, 54, 30, 7, 14, 33, 31, 7, 31, 14, 33, 7, 17, 58, 
    36, 7, 3, 40, 37, 7, 37, 3, 40, 7, 24, 1, 43, 7, 8, 22, 51, 7, 59, 13, 53, 
    7, 30, 61, 54, 7, 36, 17, 58, 7, 13, 53, 59, 7, 62, 29, 60, 7, 54, 30, 61, 
    7, 29, 60, 62, 8, 27, 40, 1, 8, 51, 47, 3, 8, 15, 52, 4, 8, 26, 57, 5, 8, 
    41, 14, 12, 8, 22, 31, 13, 8, 12, 41, 14, 8, 52, 4, 15, 8, 31, 13, 22, 8, 
    33, 53, 24, 8, 57, 5, 26, 8, 40, 1, 27, 8, 61, 58, 30, 8, 13, 22, 31, 8, 
    53, 24, 33, 8, 1, 27, 40, 8, 14, 12, 41, 8, 3, 51, 47, 8, 47, 3, 51, 8, 4, 
    15, 52, 8, 24, 33, 53, 8, 5, 26, 57, 8, 30, 61, 58, 8, 58, 30, 61]));

