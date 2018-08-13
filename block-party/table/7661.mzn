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
data =[| 62, 40, 20, 61, 42, 52,  5, 25, 37, 14, 11, 46, 36,  0, 29, 41, 32, 44, 55, 19, 39, 45, 34, 60 |
   20, 38, 14,  5, 61, 45, 18, 39, 34, 50,  1, 44, 35, 31, 27, 17, 47, 15,  0, 37, 63, 22, 55, 26 |
   27, 51, 36, 47, 21,  6, 10, 17, 43, 34, 16, 52, 12, 44, 11, 46, 42, 57, 40, 32,  2, 59, 50, 25 |
    6, 24,  8, 31, 40, 39, 59, 16, 41, 33, 45, 15, 48, 56, 20, 38, 60, 29, 14, 55,  1, 35, 51, 22 |
    3, 63, 25, 60, 26, 57, 58,  6, 12, 21, 47,  4,  1, 33, 30, 56, 23, 54, 31, 19, 18, 52, 13, 37 |
    7, 16,  4,  5, 59,  2, 12,  3, 28, 11, 58, 22, 36, 15, 13, 43, 56, 42, 21, 29,  9, 49, 53, 26 |
   13,  3, 18, 17, 50, 43, 10, 57,  9, 46,  2, 61, 28, 53, 32, 24, 49, 30, 23, 62, 48,  7, 54,  8 |
   10, 27, 23, 38, 28, 41, 30, 51, 35,  0, 48, 62,  7, 49, 19,  4, 58,  9, 24, 54, 33, 53, 63,  8 |]
;
% cubes: [5, 8, 6, 3, 1, 7, 2, 4]
% symbols: [60, 19, 5, 42, 32, 46, 39, 41, 54, 0, 26, 16, 34, 32, 14, 48, 37, 28, 42, 50, 11, 50, 22, 14]
% rotations: [7, 14, 7, 20, 20, 24, 12, 23]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 19, 40, 0, 1, 39, 46, 5, 
    1, 34, 32, 11, 1, 29, 42, 14, 1, 40, 0, 19, 1, 45, 25, 20, 1, 20, 45, 25, 
    1, 42, 14, 29, 1, 11, 34, 32, 1, 32, 11, 34, 1, 37, 55, 36, 1, 55, 36, 37, 
    1, 46, 5, 39, 1, 0, 19, 40, 1, 62, 52, 41, 1, 14, 29, 42, 1, 60, 61, 44, 1, 
    25, 20, 45, 1, 5, 39, 46, 1, 41, 62, 52, 1, 36, 37, 55, 1, 61, 44, 60, 1, 
    44, 60, 61, 1, 52, 41, 62, 2, 35, 34, 0, 2, 55, 47, 1, 2, 15, 26, 5, 2, 22, 
    39, 14, 2, 26, 5, 15, 2, 20, 45, 17, 2, 63, 44, 18, 2, 45, 17, 20, 2, 39, 
    14, 22, 2, 5, 15, 26, 2, 61, 50, 27, 2, 37, 38, 31, 2, 0, 35, 34, 2, 34, 0, 
    35, 2, 38, 31, 37, 2, 31, 37, 38, 2, 14, 22, 39, 2, 18, 63, 44, 2, 17, 20, 
    45, 2, 1, 55, 47, 2, 27, 61, 50, 2, 47, 1, 55, 2, 50, 27, 61, 2, 44, 18, 
    63, 3, 52, 10, 2, 3, 46, 27, 6, 3, 2, 52, 10, 3, 21, 34, 11, 3, 43, 40, 12, 
    3, 50, 42, 16, 3, 36, 59, 17, 3, 34, 11, 21, 3, 47, 57, 25, 3, 6, 46, 27, 
    3, 51, 44, 32, 3, 11, 21, 34, 3, 59, 17, 36, 3, 12, 43, 40, 3, 16, 50, 42, 
    3, 40, 12, 43, 3, 32, 51, 44, 3, 27, 6, 46, 3, 57, 25, 47, 3, 42, 16, 50, 
    3, 44, 32, 51, 3, 10, 2, 52, 3, 25, 47, 57, 3, 17, 36, 59, 4, 15, 59, 1, 4, 
    39, 38, 6, 4, 35, 16, 8, 4, 48, 41, 14, 4, 59, 1, 15, 4, 8, 35, 16, 4, 40, 
    33, 20, 4, 31, 29, 22, 4, 56, 55, 24, 4, 22, 31, 29, 4, 29, 22, 31, 4, 20, 
    40, 33, 4, 16, 8, 35, 4, 6, 39, 38, 4, 38, 6, 39, 4, 33, 20, 40, 4, 14, 48, 
    41, 4, 51, 60, 45, 4, 41, 14, 48, 4, 60, 45, 51, 4, 24, 56, 55, 4, 55, 24, 
    56, 4, 1, 15, 59, 4, 45, 51, 60, 5, 12, 31, 1, 5, 57, 56, 3, 5, 58, 18, 4, 
    5, 25, 52, 6, 5, 31, 1, 12, 5, 23, 47, 13, 5, 4, 58, 18, 5, 63, 33, 19, 5, 
    30, 26, 21, 5, 47, 13, 23, 5, 52, 6, 25, 5, 21, 30, 26, 5, 26, 21, 30, 5, 
    1, 12, 31, 5, 19, 63, 33, 5, 60, 54, 37, 5, 13, 23, 47, 5, 6, 25, 52, 5, 
    37, 60, 54, 5, 3, 57, 56, 5, 56, 3, 57, 5, 18, 4, 58, 5, 54, 37, 60, 5, 33, 
    19, 63, 6, 43, 7, 2, 6, 4, 49, 3, 6, 49, 3, 4, 6, 42, 26, 5, 6, 2, 43, 7, 
    6, 22, 12, 9, 6, 13, 59, 11, 6, 9, 22, 12, 6, 59, 11, 13, 6, 29, 16, 15, 6, 
    15, 29, 16, 6, 36, 28, 21, 6, 12, 9, 22, 6, 5, 42, 26, 6, 21, 36, 28, 6, 
    16, 15, 29, 6, 28, 21, 36, 6, 26, 5, 42, 6, 7, 2, 43, 6, 3, 4, 49, 6, 56, 
    58, 53, 6, 58, 53, 56, 6, 53, 56, 58, 6, 11, 13, 59, 7, 54, 49, 2, 7, 53, 
    62, 3, 7, 57, 18, 7, 7, 17, 30, 8, 7, 23, 28, 9, 7, 48, 61, 10, 7, 43, 24, 
    13, 7, 30, 8, 17, 7, 7, 57, 18, 7, 28, 9, 23, 7, 13, 43, 24, 7, 9, 23, 28, 
    7, 8, 17, 30, 7, 50, 46, 32, 7, 24, 13, 43, 7, 32, 50, 46, 7, 61, 10, 48, 
    7, 2, 54, 49, 7, 46, 32, 50, 7, 62, 3, 53, 7, 49, 2, 54, 7, 18, 7, 57, 7, 
    10, 48, 61, 7, 3, 53, 62, 8, 19, 28, 0, 8, 10, 41, 4, 8, 35, 24, 7, 8, 38, 
    9, 8, 8, 8, 38, 9, 8, 41, 4, 10, 8, 28, 0, 19, 8, 53, 51, 23, 8, 7, 35, 24, 
    8, 49, 54, 27, 8, 0, 19, 28, 8, 33, 62, 30, 8, 62, 30, 33, 8, 24, 7, 35, 8, 
    9, 8, 38, 8, 4, 10, 41, 8, 63, 58, 48, 8, 54, 27, 49, 8, 23, 53, 51, 8, 51, 
    23, 53, 8, 27, 49, 54, 8, 48, 63, 58, 8, 30, 33, 62, 8, 58, 48, 63]));

