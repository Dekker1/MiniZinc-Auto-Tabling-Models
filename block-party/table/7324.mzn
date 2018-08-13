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
data =[| 30,  7, 63, 61, 57, 62, 12,  5, 55, 16, 49, 42, 54, 18, 13, 29, 41, 15,  6,  3, 25, 22,  0, 11 |
   29, 59, 53, 45, 57, 43,  8, 36, 22,  3, 35, 50, 41,  9, 27, 37, 10, 61, 26, 60, 42, 16, 48, 39 |
    6, 46, 22, 24, 14,  0, 29, 39, 33, 10, 32, 35, 53, 30,  9, 58,  8,  7, 62,  5, 28, 11, 20,  1 |
   27, 60,  2, 56, 32, 47, 63, 26, 18, 23, 21,  5, 49, 43, 44,  3, 39, 13, 11, 40, 19, 51, 48, 20 |
   60, 61, 37, 19, 47, 27, 24, 28,  0, 25, 43, 36, 53, 45, 33, 31, 10, 63, 35, 12, 51, 58, 23, 52 |
   48, 15, 33,  4,  8, 57, 56,  6, 49,  7, 28, 38, 47, 14, 30, 51, 12, 41, 34, 59, 20, 37, 50, 17 |
   59, 32, 62, 31, 42, 16, 58,  4, 54, 40, 36, 17, 45, 19, 44, 14,  1,  2, 38, 34, 46, 55, 21, 52 |
   40, 54, 21, 13, 17,  1, 23, 44,  2, 46, 38, 24, 50, 26, 31, 18, 15,  4, 25, 56, 55, 34, 52,  9 |]
;
% cubes: [1, 5, 3, 8, 4, 7, 2, 6]
% symbols: [29, 35, 58, 4, 21, 16, 27, 30, 30, 0, 0, 9, 39, 14, 57, 7, 62, 53, 6, 13, 48, 59, 3, 8]
% rotations: [13, 19, 13, 17, 22, 11, 14, 14]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 41, 49, 0, 1, 7, 18, 3, 1, 
    63, 22, 5, 1, 54, 55, 6, 1, 18, 3, 7, 1, 61, 15, 11, 1, 25, 42, 12, 1, 57, 
    16, 13, 1, 11, 61, 15, 1, 13, 57, 16, 1, 3, 7, 18, 1, 5, 63, 22, 1, 42, 12, 
    25, 1, 30, 62, 29, 1, 62, 29, 30, 1, 49, 0, 41, 1, 12, 25, 42, 1, 0, 41, 
    49, 1, 55, 6, 54, 1, 6, 54, 55, 1, 16, 13, 57, 1, 15, 11, 61, 1, 29, 30, 
    62, 1, 22, 5, 63, 2, 27, 57, 3, 2, 42, 50, 8, 2, 60, 59, 9, 2, 35, 48, 10, 
    2, 36, 53, 16, 2, 26, 41, 22, 2, 41, 22, 26, 2, 57, 3, 27, 2, 43, 37, 29, 
    2, 48, 10, 35, 2, 53, 16, 36, 2, 29, 43, 37, 2, 45, 61, 39, 2, 22, 26, 41, 
    2, 50, 8, 42, 2, 37, 29, 43, 2, 61, 39, 45, 2, 10, 35, 48, 2, 8, 42, 50, 2, 
    16, 36, 53, 2, 3, 27, 57, 2, 9, 60, 59, 2, 59, 9, 60, 2, 39, 45, 61, 3, 58, 
    6, 0, 3, 24, 7, 1, 3, 46, 30, 5, 3, 0, 58, 6, 3, 1, 24, 7, 3, 32, 20, 8, 3, 
    14, 10, 9, 3, 9, 14, 10, 3, 39, 22, 11, 3, 10, 9, 14, 3, 8, 32, 20, 3, 11, 
    39, 22, 3, 7, 1, 24, 3, 35, 29, 28, 3, 28, 35, 29, 3, 5, 46, 30, 3, 20, 8, 
    32, 3, 62, 53, 33, 3, 29, 28, 35, 3, 22, 11, 39, 3, 30, 5, 46, 3, 33, 62, 
    53, 3, 6, 0, 58, 3, 53, 33, 62, 4, 51, 26, 2, 4, 27, 47, 3, 4, 63, 19, 5, 
    4, 49, 18, 11, 4, 20, 56, 13, 4, 11, 49, 18, 4, 5, 63, 19, 4, 56, 13, 20, 
    4, 48, 39, 21, 4, 44, 32, 23, 4, 2, 51, 26, 4, 47, 3, 27, 4, 23, 44, 32, 4, 
    21, 48, 39, 4, 60, 43, 40, 4, 40, 60, 43, 4, 32, 23, 44, 4, 3, 27, 47, 4, 
    39, 21, 48, 4, 18, 11, 49, 4, 26, 2, 51, 4, 13, 20, 56, 4, 43, 40, 60, 4, 
    19, 5, 63, 5, 35, 53, 0, 5, 43, 23, 10, 5, 61, 45, 12, 5, 63, 52, 19, 5, 
    10, 43, 23, 5, 51, 36, 24, 5, 33, 47, 25, 5, 31, 60, 27, 5, 37, 58, 28, 5, 
    60, 27, 31, 5, 47, 25, 33, 5, 53, 0, 35, 5, 24, 51, 36, 5, 58, 28, 37, 5, 
    23, 10, 43, 5, 12, 61, 45, 5, 25, 33, 47, 5, 36, 24, 51, 5, 19, 63, 52, 5, 
    0, 35, 53, 5, 28, 37, 58, 5, 27, 31, 60, 5, 45, 12, 61, 5, 52, 19, 63, 6, 
    41, 17, 4, 6, 33, 37, 6, 6, 30, 8, 7, 6, 7, 30, 8, 6, 28, 50, 12, 6, 59, 
    15, 14, 6, 14, 59, 15, 6, 4, 41, 17, 6, 38, 56, 20, 6, 50, 12, 28, 6, 8, 7, 
    30, 6, 37, 6, 33, 6, 47, 49, 34, 6, 6, 33, 37, 6, 56, 20, 38, 6, 17, 4, 41, 
    6, 49, 34, 47, 6, 57, 51, 48, 6, 34, 47, 49, 6, 12, 28, 50, 6, 48, 57, 51, 
    6, 20, 38, 56, 6, 51, 48, 57, 6, 15, 14, 59, 7, 36, 21, 1, 7, 52, 31, 2, 7, 
    62, 55, 4, 7, 59, 16, 14, 7, 14, 59, 16, 7, 58, 46, 17, 7, 34, 32, 19, 7, 
    1, 36, 21, 7, 2, 52, 31, 7, 19, 34, 32, 7, 32, 19, 34, 7, 21, 1, 36, 7, 45, 
    54, 38, 7, 44, 42, 40, 7, 40, 44, 42, 7, 42, 40, 44, 7, 54, 38, 45, 7, 17, 
    58, 46, 7, 31, 2, 52, 7, 38, 45, 54, 7, 4, 62, 55, 7, 46, 17, 58, 7, 16, 
    14, 59, 7, 55, 4, 62, 8, 18, 40, 1, 8, 25, 50, 2, 8, 9, 13, 4, 8, 13, 4, 9, 
    8, 4, 9, 13, 8, 38, 52, 15, 8, 46, 31, 17, 8, 40, 1, 18, 8, 34, 44, 21, 8, 
    55, 24, 23, 8, 23, 55, 24, 8, 50, 2, 25, 8, 56, 54, 26, 8, 17, 46, 31, 8, 
    44, 21, 34, 8, 52, 15, 38, 8, 1, 18, 40, 8, 21, 34, 44, 8, 31, 17, 46, 8, 
    2, 25, 50, 8, 15, 38, 52, 8, 26, 56, 54, 8, 24, 23, 55, 8, 54, 26, 56]));

