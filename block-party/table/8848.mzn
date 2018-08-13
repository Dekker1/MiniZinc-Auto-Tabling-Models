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
data =[| 32,  4, 28, 47,  2, 54, 21,  0,  6, 40, 17, 42, 26, 50, 23, 44, 46, 55, 19, 63, 12, 41, 29, 20 |
    7, 44, 29,  3,  9, 35, 36, 30, 27, 37, 10, 39, 19, 11, 51,  0, 34, 18, 28, 32, 46,  1, 21,  8 |
   52, 47, 48, 33, 58,  4,  8,  3,  5, 16, 13, 36, 38, 42, 49, 18, 29, 41,  7, 21, 53,  6, 62, 24 |
   17, 54, 34, 24,  1, 26,  9,  7, 47, 57, 39, 50, 43, 22, 13, 15, 45, 27, 41, 30, 48, 35, 23, 20 |
    5, 23, 48, 50, 13, 10, 45, 16, 40,  2, 18,  9, 58, 11, 32, 43, 28, 51, 22,  3,  0, 57, 20, 59 |
   31, 43, 60, 52, 24, 25, 37, 49, 35, 51, 15, 62,  1, 63, 54,  6,  8, 27, 58, 39, 14, 61, 33, 56 |
    5, 17, 25, 12, 57, 63, 62, 46, 31, 33, 45, 60, 30, 19, 53, 34,  4, 56, 61, 40, 38, 59, 55, 14 |
   12, 38, 10, 56, 61, 44, 22, 60, 49, 26, 52, 36,  2, 16, 53, 15, 31, 42, 37, 55, 11, 25, 59, 14 |]
;
% cubes: [1, 8, 3, 6, 5, 2, 7, 4]
% symbols: [47, 36, 42, 33, 3, 34, 17, 48, 55, 11, 47, 8, 11, 10, 19, 9, 20, 22, 21, 15, 23, 21, 40, 50]
% rotations: [7, 21, 16, 2, 18, 20, 6, 1]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 28, 41, 0, 1, 40, 23, 2, 
    1, 50, 63, 4, 1, 19, 26, 6, 1, 42, 21, 12, 1, 29, 46, 17, 1, 26, 6, 19, 1, 
    47, 55, 20, 1, 12, 42, 21, 1, 2, 40, 23, 1, 6, 19, 26, 1, 41, 0, 28, 1, 46, 
    17, 29, 1, 54, 44, 32, 1, 23, 2, 40, 1, 0, 28, 41, 1, 21, 12, 42, 1, 32, 
    54, 44, 1, 17, 29, 46, 1, 55, 20, 47, 1, 63, 4, 50, 1, 44, 32, 54, 1, 20, 
    47, 55, 1, 4, 50, 63, 2, 7, 35, 0, 2, 30, 29, 1, 2, 18, 8, 3, 2, 35, 0, 7, 
    2, 3, 18, 8, 2, 37, 51, 9, 2, 21, 34, 10, 2, 32, 44, 11, 2, 8, 3, 18, 2, 
    27, 28, 19, 2, 34, 10, 21, 2, 28, 19, 27, 2, 19, 27, 28, 2, 1, 30, 29, 2, 
    29, 1, 30, 2, 44, 11, 32, 2, 10, 21, 34, 2, 0, 7, 35, 2, 46, 39, 36, 2, 51, 
    9, 37, 2, 36, 46, 39, 2, 11, 32, 44, 2, 39, 36, 46, 2, 9, 37, 51, 3, 48, 6, 
    3, 3, 18, 52, 4, 3, 7, 38, 5, 3, 3, 48, 6, 3, 38, 5, 7, 3, 53, 36, 8, 3, 
    62, 29, 13, 3, 49, 58, 16, 3, 52, 4, 18, 3, 47, 42, 21, 3, 33, 41, 24, 3, 
    13, 62, 29, 3, 41, 24, 33, 3, 8, 53, 36, 3, 5, 7, 38, 3, 24, 33, 41, 3, 21, 
    47, 42, 3, 42, 21, 47, 3, 6, 3, 48, 3, 58, 16, 49, 3, 4, 18, 52, 3, 36, 8, 
    53, 3, 16, 49, 58, 3, 29, 13, 62, 4, 57, 13, 1, 4, 34, 35, 7, 4, 48, 50, 9, 
    4, 1, 57, 13, 4, 17, 26, 15, 4, 26, 15, 17, 4, 24, 27, 20, 4, 30, 54, 22, 
    4, 45, 39, 23, 4, 27, 20, 24, 4, 15, 17, 26, 4, 20, 24, 27, 4, 54, 22, 30, 
    4, 35, 7, 34, 4, 7, 34, 35, 4, 23, 45, 39, 4, 43, 47, 41, 4, 47, 41, 43, 4, 
    39, 23, 45, 4, 41, 43, 47, 4, 50, 9, 48, 4, 9, 48, 50, 4, 22, 30, 54, 4, 
    13, 1, 57, 5, 9, 45, 0, 5, 32, 13, 2, 5, 23, 11, 3, 5, 10, 43, 5, 5, 45, 0, 
    9, 5, 43, 5, 10, 5, 3, 23, 11, 5, 2, 32, 13, 5, 48, 57, 16, 5, 20, 28, 18, 
    5, 28, 18, 20, 5, 58, 40, 22, 5, 11, 3, 23, 5, 18, 20, 28, 5, 13, 2, 32, 5, 
    22, 58, 40, 5, 5, 10, 43, 5, 0, 9, 45, 5, 57, 16, 48, 5, 51, 59, 50, 5, 59, 
    50, 51, 5, 16, 48, 57, 5, 40, 22, 58, 5, 50, 51, 59, 6, 35, 58, 1, 6, 31, 
    25, 6, 6, 15, 33, 8, 6, 62, 37, 14, 6, 33, 8, 15, 6, 51, 54, 24, 6, 6, 31, 
    25, 6, 56, 52, 27, 6, 25, 6, 31, 6, 8, 15, 33, 6, 58, 1, 35, 6, 14, 62, 37, 
    6, 43, 63, 39, 6, 63, 39, 43, 6, 60, 61, 49, 6, 54, 24, 51, 6, 27, 56, 52, 
    6, 24, 51, 54, 6, 52, 27, 56, 6, 1, 35, 58, 6, 61, 49, 60, 6, 49, 60, 61, 
    6, 37, 14, 62, 6, 39, 43, 63, 7, 45, 55, 4, 7, 63, 34, 5, 7, 56, 14, 12, 7, 
    12, 56, 14, 7, 19, 40, 17, 7, 40, 17, 19, 7, 59, 46, 25, 7, 31, 61, 30, 7, 
    61, 30, 31, 7, 53, 57, 33, 7, 5, 63, 34, 7, 60, 62, 38, 7, 17, 19, 40, 7, 
    55, 4, 45, 7, 25, 59, 46, 7, 57, 33, 53, 7, 4, 45, 55, 7, 14, 12, 56, 7, 
    33, 53, 57, 7, 46, 25, 59, 7, 62, 38, 60, 7, 30, 31, 61, 7, 38, 60, 62, 7, 
    34, 5, 63, 8, 49, 37, 2, 8, 25, 60, 10, 8, 36, 22, 11, 8, 44, 15, 12, 8, 
    56, 42, 14, 8, 12, 44, 15, 8, 55, 38, 16, 8, 11, 36, 22, 8, 60, 10, 25, 8, 
    53, 61, 26, 8, 52, 59, 31, 8, 22, 11, 36, 8, 2, 49, 37, 8, 16, 55, 38, 8, 
    14, 56, 42, 8, 15, 12, 44, 8, 37, 2, 49, 8, 59, 31, 52, 8, 61, 26, 53, 8, 
    38, 16, 55, 8, 42, 14, 56, 8, 31, 52, 59, 8, 10, 25, 60, 8, 26, 53, 61]));

