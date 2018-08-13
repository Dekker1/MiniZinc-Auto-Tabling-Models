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
data =[| 29,  9, 38, 49,  7, 32, 34, 52, 25,  2, 43, 42,  4, 17, 31, 56, 58, 62, 21, 28, 37, 50, 60, 51 |
   47, 10, 39, 28, 31, 17, 61, 23, 29, 13,  1, 50, 49,  9, 37,  2, 16, 20, 26, 33,  4, 34, 46, 44 |
    5, 57,  4, 56, 47,  7, 36, 42, 18, 61, 26, 30,  0, 55, 16, 53, 33, 54, 45, 60, 12, 25, 31, 50 |
   15, 14, 59, 39, 54, 27, 35, 52, 49, 10,  5, 48, 20,  6, 19, 16, 24, 61, 37,  3, 44, 36, 11, 17 |
   62,  0,  2, 18, 45, 33, 41, 52, 48,  5, 40, 21, 14, 46, 27, 26, 56, 59, 28, 12, 55, 11, 53, 42 |
   43, 12, 58,  9, 18, 57, 60, 46, 45, 32, 39, 53,  6,  1, 11, 41, 29, 54, 14, 62, 63,  8, 47, 22 |
   55, 24, 34, 51, 22, 32, 23, 20, 63,  1, 35,  0,  7, 40, 36, 59,  3,  8, 19, 38, 15, 10, 30, 13 |
   30,  3, 22, 51, 23, 15, 27, 41, 19, 13, 44, 63, 35,  8, 58,  6, 25, 21, 38, 40, 48, 57, 24, 43 |]
;
% cubes: [8, 5, 2, 6, 1, 3, 4, 7]
% symbols: [44, 45, 46, 47, 51, 0, 17, 34, 24, 27, 1, 29, 62, 18, 39, 20, 25, 5, 16, 39, 49, 45, 61, 10]
% rotations: [22, 10, 2, 2, 3, 15, 3, 8]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 31, 7, 2, 1, 25, 21, 4, 1, 
    2, 31, 7, 1, 17, 28, 9, 1, 28, 9, 17, 1, 4, 25, 21, 1, 21, 4, 25, 1, 9, 17, 
    28, 1, 32, 56, 29, 1, 7, 2, 31, 1, 56, 29, 32, 1, 37, 42, 34, 1, 42, 34, 
    37, 1, 50, 52, 38, 1, 34, 37, 42, 1, 60, 58, 43, 1, 62, 51, 49, 1, 52, 38, 
    50, 1, 49, 62, 51, 1, 38, 50, 52, 1, 29, 32, 56, 1, 43, 60, 58, 1, 58, 43, 
    60, 1, 51, 49, 62, 2, 46, 16, 1, 2, 47, 17, 2, 2, 50, 61, 4, 2, 33, 10, 9, 
    2, 9, 33, 10, 2, 37, 31, 13, 2, 1, 46, 16, 2, 2, 47, 17, 2, 44, 28, 20, 2, 
    39, 34, 23, 2, 49, 29, 26, 2, 20, 44, 28, 2, 26, 49, 29, 2, 13, 37, 31, 2, 
    10, 9, 33, 2, 23, 39, 34, 2, 31, 13, 37, 2, 34, 23, 39, 2, 28, 20, 44, 2, 
    16, 1, 46, 2, 17, 2, 47, 2, 29, 26, 49, 2, 61, 4, 50, 2, 4, 50, 61, 3, 18, 
    45, 0, 3, 25, 42, 4, 3, 7, 53, 5, 3, 53, 5, 7, 3, 30, 36, 12, 3, 47, 61, 
    16, 3, 45, 0, 18, 3, 42, 4, 25, 3, 31, 33, 26, 3, 36, 12, 30, 3, 33, 26, 
    31, 3, 26, 31, 33, 3, 12, 30, 36, 3, 4, 25, 42, 3, 0, 18, 45, 3, 61, 16, 
    47, 3, 56, 54, 50, 3, 5, 7, 53, 3, 50, 56, 54, 3, 60, 57, 55, 3, 54, 50, 
    56, 3, 55, 60, 57, 3, 57, 55, 60, 3, 16, 47, 61, 4, 14, 6, 3, 4, 11, 24, 5, 
    4, 3, 14, 6, 4, 19, 54, 10, 4, 24, 5, 11, 4, 6, 3, 14, 4, 27, 16, 15, 4, 
    15, 27, 16, 4, 39, 61, 17, 4, 54, 10, 19, 4, 49, 37, 20, 4, 5, 11, 24, 4, 
    16, 15, 27, 4, 44, 48, 35, 4, 52, 59, 36, 4, 20, 49, 37, 4, 61, 17, 39, 4, 
    48, 35, 44, 4, 35, 44, 48, 4, 37, 20, 49, 4, 59, 36, 52, 4, 10, 19, 54, 4, 
    36, 52, 59, 4, 17, 39, 61, 5, 46, 12, 0, 5, 11, 52, 2, 5, 27, 45, 5, 5, 52, 
    2, 11, 5, 0, 46, 12, 5, 48, 28, 14, 5, 59, 42, 18, 5, 41, 55, 21, 5, 62, 
    33, 26, 5, 45, 5, 27, 5, 14, 48, 28, 5, 26, 62, 33, 5, 53, 56, 40, 5, 55, 
    21, 41, 5, 18, 59, 42, 5, 5, 27, 45, 5, 12, 0, 46, 5, 28, 14, 48, 5, 2, 11, 
    52, 5, 56, 40, 53, 5, 21, 41, 55, 5, 40, 53, 56, 5, 42, 18, 59, 5, 33, 26, 
    62, 6, 62, 12, 1, 6, 45, 14, 6, 6, 46, 58, 8, 6, 54, 22, 9, 6, 18, 32, 11, 
    6, 1, 62, 12, 6, 6, 45, 14, 6, 32, 11, 18, 6, 9, 54, 22, 6, 39, 47, 29, 6, 
    11, 18, 32, 6, 47, 29, 39, 6, 43, 57, 41, 6, 57, 41, 43, 6, 14, 6, 45, 6, 
    58, 8, 46, 6, 29, 39, 47, 6, 60, 63, 53, 6, 22, 9, 54, 6, 41, 43, 57, 6, 8, 
    46, 58, 6, 63, 53, 60, 6, 12, 1, 62, 6, 53, 60, 63, 7, 23, 15, 0, 7, 36, 
    22, 1, 7, 35, 30, 3, 7, 63, 19, 7, 7, 13, 51, 8, 7, 20, 34, 10, 7, 51, 8, 
    13, 7, 0, 23, 15, 7, 7, 63, 19, 7, 34, 10, 20, 7, 1, 36, 22, 7, 15, 0, 23, 
    7, 40, 38, 24, 7, 3, 35, 30, 7, 59, 55, 32, 7, 10, 20, 34, 7, 30, 3, 35, 7, 
    22, 1, 36, 7, 24, 40, 38, 7, 38, 24, 40, 7, 8, 13, 51, 7, 32, 59, 55, 7, 
    55, 32, 59, 7, 19, 7, 63, 8, 8, 40, 3, 8, 30, 15, 6, 8, 40, 3, 8, 8, 58, 
    23, 13, 8, 6, 30, 15, 8, 38, 35, 19, 8, 43, 51, 21, 8, 57, 41, 22, 8, 13, 
    58, 23, 8, 25, 44, 24, 8, 44, 24, 25, 8, 48, 63, 27, 8, 15, 6, 30, 8, 19, 
    38, 35, 8, 35, 19, 38, 8, 3, 8, 40, 8, 22, 57, 41, 8, 51, 21, 43, 8, 24, 
    25, 44, 8, 63, 27, 48, 8, 21, 43, 51, 8, 41, 22, 57, 8, 23, 13, 58, 8, 27, 
    48, 63]));

