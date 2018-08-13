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
data =[|  6, 36, 47, 53,  3, 41,  1, 13, 34, 18, 60, 23, 63,  5, 37, 52, 50, 57, 19, 22, 46, 17, 24, 11 |
   27, 34, 36, 30, 55, 58, 52, 32,  5, 57, 60, 33, 41, 42, 35,  8, 40,  9, 37,  2, 50, 39, 24, 28 |
   24,  6,  2, 28, 47, 37, 12, 44, 58, 36, 43, 32, 38, 61, 48, 49, 57, 40,  3, 23, 42, 50, 62,  1 |
    7, 59,  0, 45, 60, 22, 10, 25, 15, 38, 42, 54, 14, 51, 43,  2, 12,  4, 23, 48, 41, 21, 30,  6 |
    1, 63, 21, 18,  8, 48, 29, 56, 15, 35, 12, 43, 58, 19, 10, 33, 49, 14,  9,  4, 53, 39, 13, 47 |
   18, 53, 38, 46, 27, 34, 20, 16, 56, 32, 51, 55, 22, 19, 40, 28, 54, 62,  7,  9, 59,  5, 26, 31 |
   54, 21, 20, 45, 33,  7, 35, 49, 56, 16, 17, 10,  0,  8, 14, 63, 25, 26, 44, 31, 29, 61, 11, 13 |
   44, 20, 30, 27,  4, 11, 59, 25, 16, 39, 51, 15, 45,  3, 52, 46, 26, 31, 55, 61, 17, 62,  0, 29 |]
;
% cubes: [7, 8, 5, 3, 4, 1, 6, 2]
% symbols: [13, 4, 10, 3, 43, 46, 32, 37, 45, 52, 35, 38, 38, 23, 40, 5, 26, 39, 8, 58, 60, 1, 27, 41]
% rotations: [3, 10, 14, 19, 14, 1, 24, 19]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 46, 23, 1, 1, 18, 37, 3, 
    1, 22, 36, 5, 1, 41, 52, 6, 1, 53, 57, 11, 1, 47, 17, 13, 1, 13, 47, 17, 1, 
    37, 3, 18, 1, 63, 34, 19, 1, 36, 5, 22, 1, 1, 46, 23, 1, 50, 60, 24, 1, 19, 
    63, 34, 1, 5, 22, 36, 1, 3, 18, 37, 1, 52, 6, 41, 1, 23, 1, 46, 1, 17, 13, 
    47, 1, 60, 24, 50, 1, 6, 41, 52, 1, 57, 11, 53, 1, 11, 53, 57, 1, 24, 50, 
    60, 1, 34, 19, 63, 2, 34, 42, 2, 2, 37, 41, 5, 2, 27, 58, 8, 2, 28, 30, 9, 
    2, 40, 60, 24, 2, 58, 8, 27, 2, 30, 9, 28, 2, 9, 28, 30, 2, 36, 39, 32, 2, 
    52, 50, 33, 2, 42, 2, 34, 2, 55, 57, 35, 2, 39, 32, 36, 2, 41, 5, 37, 2, 
    32, 36, 39, 2, 60, 24, 40, 2, 5, 37, 41, 2, 2, 34, 42, 2, 33, 52, 50, 2, 
    50, 33, 52, 2, 57, 35, 55, 2, 35, 55, 57, 2, 8, 27, 58, 2, 24, 40, 60, 3, 
    28, 40, 1, 3, 50, 44, 2, 3, 38, 58, 3, 3, 61, 23, 6, 3, 42, 32, 12, 3, 6, 
    61, 23, 3, 37, 49, 24, 3, 40, 1, 28, 3, 12, 42, 32, 3, 48, 47, 36, 3, 49, 
    24, 37, 3, 58, 3, 38, 3, 1, 28, 40, 3, 32, 12, 42, 3, 62, 57, 43, 3, 2, 50, 
    44, 3, 36, 48, 47, 3, 47, 36, 48, 3, 24, 37, 49, 3, 44, 2, 50, 3, 43, 62, 
    57, 3, 3, 38, 58, 3, 23, 6, 61, 3, 57, 43, 62, 4, 21, 25, 0, 4, 7, 22, 2, 
    4, 6, 45, 4, 4, 45, 4, 6, 4, 22, 2, 7, 4, 41, 54, 10, 4, 42, 30, 12, 4, 15, 
    23, 14, 4, 23, 14, 15, 4, 25, 0, 21, 4, 2, 7, 22, 4, 14, 15, 23, 4, 0, 21, 
    25, 4, 12, 42, 30, 4, 43, 60, 38, 4, 54, 10, 41, 4, 30, 12, 42, 4, 60, 38, 
    43, 4, 4, 6, 45, 4, 59, 51, 48, 4, 48, 59, 51, 4, 10, 41, 54, 4, 51, 48, 
    59, 4, 38, 43, 60, 5, 48, 33, 1, 5, 63, 19, 4, 5, 35, 10, 8, 5, 58, 15, 9, 
    5, 8, 35, 10, 5, 13, 49, 12, 5, 49, 12, 13, 5, 47, 18, 14, 5, 9, 58, 15, 5, 
    14, 47, 18, 5, 4, 63, 19, 5, 39, 56, 21, 5, 53, 43, 29, 5, 1, 48, 33, 5, 
    10, 8, 35, 5, 56, 21, 39, 5, 29, 53, 43, 5, 18, 14, 47, 5, 33, 1, 48, 5, 
    12, 13, 49, 5, 43, 29, 53, 5, 21, 39, 56, 5, 15, 9, 58, 5, 19, 4, 63, 6, 
    16, 38, 5, 6, 22, 56, 7, 6, 53, 19, 9, 6, 38, 5, 16, 6, 34, 28, 18, 6, 9, 
    53, 19, 6, 59, 55, 20, 6, 56, 7, 22, 6, 54, 51, 26, 6, 32, 40, 27, 6, 18, 
    34, 28, 6, 46, 62, 31, 6, 40, 27, 32, 6, 28, 18, 34, 6, 5, 16, 38, 6, 27, 
    32, 40, 6, 62, 31, 46, 6, 26, 54, 51, 6, 19, 9, 53, 6, 51, 26, 54, 6, 20, 
    59, 55, 6, 7, 22, 56, 6, 55, 20, 59, 6, 31, 46, 62, 7, 56, 44, 0, 7, 63, 
    54, 7, 7, 31, 21, 8, 7, 35, 29, 10, 7, 25, 17, 11, 7, 45, 26, 13, 7, 33, 
    16, 14, 7, 14, 33, 16, 7, 11, 25, 17, 7, 61, 49, 20, 7, 8, 31, 21, 7, 17, 
    11, 25, 7, 13, 45, 26, 7, 10, 35, 29, 7, 21, 8, 31, 7, 16, 14, 33, 7, 29, 
    10, 35, 7, 0, 56, 44, 7, 26, 13, 45, 7, 20, 61, 49, 7, 7, 63, 54, 7, 44, 0, 
    56, 7, 49, 20, 61, 7, 54, 7, 63, 8, 26, 51, 0, 8, 61, 20, 3, 8, 39, 52, 4, 
    8, 46, 44, 11, 8, 59, 17, 15, 8, 55, 45, 16, 8, 15, 59, 17, 8, 3, 61, 20, 
    8, 30, 62, 25, 8, 51, 0, 26, 8, 31, 29, 27, 8, 27, 31, 29, 8, 62, 25, 30, 
    8, 29, 27, 31, 8, 52, 4, 39, 8, 11, 46, 44, 8, 16, 55, 45, 8, 44, 11, 46, 
    8, 0, 26, 51, 8, 4, 39, 52, 8, 45, 16, 55, 8, 17, 15, 59, 8, 20, 3, 61, 8, 
    25, 30, 62]));

