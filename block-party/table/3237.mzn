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
data =[| 10, 56, 12,  7, 39, 22, 33, 59, 21,  6, 30, 55, 27,  3, 41, 44, 57,  4, 28, 26, 60, 49, 15,  2 |
   33, 22, 38, 51, 57, 10,  1, 48, 18,  0, 21, 23, 14,  8, 27, 30, 26, 34, 11, 52, 12, 40, 63, 45 |
   34, 38, 12, 57, 54,  6, 61, 43, 58, 53, 20,  7, 25, 60, 33,  0, 40,  9, 37, 19, 15,  8, 30, 51 |
   24, 46, 15, 16, 58,  0,  7, 53, 42, 54, 21,  5, 38, 13, 45, 55, 29, 22, 56, 50, 11, 59, 34, 17 |
   39, 46, 52, 48, 41,  6, 51, 49, 32, 60, 20, 53,  2,  1, 40, 45, 13, 26, 29, 27, 50, 56, 63,  4 |
   39,  5, 52, 61, 41, 19, 24, 20, 48, 23, 36, 63, 11, 13, 42, 46, 49, 54, 62, 37, 47, 31, 35,  8 |
   61, 44, 43, 42, 29, 16, 37,  4, 25, 62, 32,  9,  5, 36, 10, 24,  3, 31, 14, 28, 47, 35, 17, 18 |
   19, 23, 16, 14, 32, 50, 44, 18, 25, 55, 43,  1, 28,  2,  9, 58, 35, 62,  3, 59, 36, 31, 47, 17 |]
;
% cubes: [4, 8, 5, 7, 2, 6, 3, 1]
% symbols: [42, 58, 26, 10, 22, 54, 38, 6, 56, 50, 48, 29, 52, 8, 60, 39, 38, 19, 4, 62, 8, 61, 19, 41]
% rotations: [23, 13, 17, 14, 6, 17, 6, 24]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 7, 4, 2, 1, 26, 56, 3, 1, 
    2, 7, 4, 1, 41, 39, 6, 1, 4, 2, 7, 1, 22, 44, 10, 1, 49, 59, 12, 1, 57, 30, 
    15, 1, 28, 27, 21, 1, 44, 10, 22, 1, 56, 3, 26, 1, 21, 28, 27, 1, 27, 21, 
    28, 1, 15, 57, 30, 1, 60, 55, 33, 1, 6, 41, 39, 1, 39, 6, 41, 1, 10, 22, 
    44, 1, 59, 12, 49, 1, 33, 60, 55, 1, 3, 26, 56, 1, 30, 15, 57, 1, 12, 49, 
    59, 1, 55, 33, 60, 2, 27, 57, 0, 2, 12, 23, 1, 2, 52, 22, 8, 2, 30, 33, 10, 
    2, 14, 18, 11, 2, 23, 1, 12, 2, 18, 11, 14, 2, 11, 14, 18, 2, 63, 26, 21, 
    2, 8, 52, 22, 2, 1, 12, 23, 2, 21, 63, 26, 2, 57, 0, 27, 2, 33, 10, 30, 2, 
    10, 30, 33, 2, 45, 51, 34, 2, 40, 48, 38, 2, 48, 38, 40, 2, 51, 34, 45, 2, 
    38, 40, 48, 2, 34, 45, 51, 2, 22, 8, 52, 2, 0, 27, 57, 2, 26, 21, 63, 3, 
    34, 6, 0, 3, 0, 34, 6, 3, 61, 15, 7, 3, 43, 12, 8, 3, 51, 57, 9, 3, 8, 43, 
    12, 3, 7, 61, 15, 3, 38, 60, 19, 3, 30, 40, 20, 3, 58, 37, 25, 3, 40, 20, 
    30, 3, 54, 53, 33, 3, 6, 0, 34, 3, 25, 58, 37, 3, 60, 19, 38, 3, 20, 30, 
    40, 3, 12, 8, 43, 3, 57, 9, 51, 3, 33, 54, 53, 3, 53, 33, 54, 3, 9, 51, 57, 
    3, 37, 25, 58, 3, 19, 38, 60, 3, 15, 7, 61, 4, 55, 24, 0, 4, 7, 11, 5, 4, 
    11, 5, 7, 4, 5, 7, 11, 4, 50, 46, 13, 4, 59, 53, 15, 4, 22, 17, 16, 4, 16, 
    22, 17, 4, 34, 29, 21, 4, 17, 16, 22, 4, 0, 55, 24, 4, 21, 34, 29, 4, 29, 
    21, 34, 4, 42, 56, 38, 4, 56, 38, 42, 4, 58, 54, 45, 4, 13, 50, 46, 4, 46, 
    13, 50, 4, 15, 59, 53, 4, 45, 58, 54, 4, 24, 0, 55, 4, 38, 42, 56, 4, 54, 
    45, 58, 4, 53, 15, 59, 5, 27, 46, 1, 5, 32, 29, 2, 5, 48, 26, 4, 5, 45, 39, 
    6, 5, 20, 63, 13, 5, 63, 13, 20, 5, 4, 48, 26, 5, 46, 1, 27, 5, 2, 32, 29, 
    5, 29, 2, 32, 5, 6, 45, 39, 5, 41, 60, 40, 5, 60, 40, 41, 5, 39, 6, 45, 5, 
    1, 27, 46, 5, 26, 4, 48, 5, 52, 56, 49, 5, 53, 51, 50, 5, 50, 53, 51, 5, 
    56, 49, 52, 5, 51, 50, 53, 5, 49, 52, 56, 5, 40, 41, 60, 5, 13, 20, 63, 6, 
    13, 37, 5, 6, 61, 54, 8, 6, 48, 62, 11, 6, 37, 5, 13, 6, 46, 39, 19, 6, 52, 
    31, 20, 6, 42, 41, 23, 6, 47, 63, 24, 6, 20, 52, 31, 6, 49, 36, 35, 6, 35, 
    49, 36, 6, 5, 13, 37, 6, 19, 46, 39, 6, 23, 42, 41, 6, 41, 23, 42, 6, 39, 
    19, 46, 6, 63, 24, 47, 6, 62, 11, 48, 6, 36, 35, 49, 6, 31, 20, 52, 6, 8, 
    61, 54, 6, 54, 8, 61, 6, 11, 48, 62, 6, 24, 47, 63, 7, 32, 17, 3, 7, 43, 
    35, 4, 7, 25, 14, 5, 7, 37, 47, 9, 7, 29, 62, 10, 7, 5, 25, 14, 7, 24, 61, 
    16, 7, 3, 32, 17, 7, 42, 31, 18, 7, 61, 16, 24, 7, 14, 5, 25, 7, 44, 36, 
    28, 7, 62, 10, 29, 7, 18, 42, 31, 7, 17, 3, 32, 7, 4, 43, 35, 7, 28, 44, 
    36, 7, 47, 9, 37, 7, 31, 18, 42, 7, 35, 4, 43, 7, 36, 28, 44, 7, 9, 37, 47, 
    7, 16, 24, 61, 7, 10, 29, 62, 8, 44, 36, 1, 8, 59, 23, 2, 8, 28, 25, 3, 8, 
    32, 55, 9, 8, 62, 17, 14, 8, 31, 18, 16, 8, 14, 62, 17, 8, 16, 31, 18, 8, 
    50, 58, 19, 8, 2, 59, 23, 8, 3, 28, 25, 8, 25, 3, 28, 8, 18, 16, 31, 8, 55, 
    9, 32, 8, 43, 47, 35, 8, 1, 44, 36, 8, 47, 35, 43, 8, 36, 1, 44, 8, 35, 43, 
    47, 8, 58, 19, 50, 8, 9, 32, 55, 8, 19, 50, 58, 8, 23, 2, 59, 8, 17, 14, 
    62]));

