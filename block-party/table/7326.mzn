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
data =[| 16, 63,  9, 37, 29, 30, 31, 55, 25, 23, 60, 53, 26, 46, 13, 50, 15, 47, 28,  6, 49, 11, 48, 38 |
   44, 47, 27, 12, 41, 40, 50, 54, 43, 37,  2,  9, 51, 20, 26, 11, 17, 63, 23, 45, 34, 31, 62, 29 |
   51, 14, 11, 49, 61, 34, 24, 17, 47, 46, 38,  1,  2, 31, 32, 19, 39, 54, 37, 48, 40, 35, 10, 44 |
   48, 42, 15, 14,  5, 12, 50, 58, 56, 34,  3, 53, 20, 17, 40,  2, 30,  1, 45, 24, 62, 36, 63, 61 |
   58, 55, 49, 42, 62, 33,  5, 25, 20, 13, 44, 28, 59, 43, 21, 45, 52, 30, 29, 38, 23, 14,  1, 35 |
   60, 16, 58, 36, 57, 27, 43, 12, 46,  9, 54,  3,  0, 22, 41,  8,  7, 10, 53, 21,  4, 32, 61, 18 |
    3, 18, 32, 10, 52, 22,  8, 39,  4, 28, 42, 60, 57,  5, 56,  0, 55,  6, 24, 59, 33, 19,  7, 51 |
    0, 52, 22,  4, 56, 19, 27, 33, 13, 16, 57, 36, 41, 15,  7,  8, 21, 25, 39, 35, 18,  6, 26, 59 |]
;
% cubes: [1, 2, 4, 8, 3, 7, 5, 6]
% symbols: [28, 45, 62, 15, 31, 51, 43, 7, 26, 20, 50, 35, 14, 10, 38, 61, 25, 47, 53, 52, 48, 6, 55, 54]
% rotations: [19, 18, 1, 16, 16, 3, 16, 20]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 63, 46, 6, 1, 11, 55, 9, 
    1, 55, 9, 11, 1, 29, 23, 13, 1, 60, 48, 15, 1, 30, 50, 16, 1, 13, 29, 23, 
    1, 28, 26, 25, 1, 25, 28, 26, 1, 26, 25, 28, 1, 23, 13, 29, 1, 50, 16, 30, 
    1, 49, 53, 31, 1, 47, 38, 37, 1, 37, 47, 38, 1, 6, 63, 46, 1, 38, 37, 47, 
    1, 15, 60, 48, 1, 53, 31, 49, 1, 16, 30, 50, 1, 31, 49, 53, 1, 9, 11, 55, 
    1, 48, 15, 60, 1, 46, 6, 63, 2, 62, 17, 2, 2, 50, 34, 9, 2, 44, 40, 11, 2, 
    63, 29, 12, 2, 2, 62, 17, 2, 45, 47, 20, 2, 51, 43, 23, 2, 41, 37, 26, 2, 
    31, 54, 27, 2, 12, 63, 29, 2, 54, 27, 31, 2, 9, 50, 34, 2, 26, 41, 37, 2, 
    11, 44, 40, 2, 37, 26, 41, 2, 23, 51, 43, 2, 40, 11, 44, 2, 47, 20, 45, 2, 
    20, 45, 47, 2, 34, 9, 50, 2, 43, 23, 51, 2, 27, 31, 54, 2, 17, 2, 62, 2, 
    29, 12, 63, 3, 24, 40, 1, 3, 47, 37, 2, 3, 39, 38, 10, 3, 35, 17, 11, 3, 
    31, 48, 14, 3, 11, 35, 17, 3, 51, 34, 19, 3, 40, 1, 24, 3, 48, 14, 31, 3, 
    61, 46, 32, 3, 19, 51, 34, 3, 17, 11, 35, 3, 2, 47, 37, 3, 10, 39, 38, 3, 
    38, 10, 39, 3, 1, 24, 40, 3, 49, 54, 44, 3, 32, 61, 46, 3, 37, 2, 47, 3, 
    14, 31, 48, 3, 54, 44, 49, 3, 34, 19, 51, 3, 44, 49, 54, 3, 46, 32, 61, 4, 
    61, 14, 1, 4, 48, 12, 2, 4, 63, 30, 3, 4, 34, 40, 5, 4, 2, 48, 12, 4, 1, 
    61, 14, 4, 36, 58, 15, 4, 24, 42, 17, 4, 56, 45, 20, 4, 42, 17, 24, 4, 3, 
    63, 30, 4, 40, 5, 34, 4, 58, 15, 36, 4, 5, 34, 40, 4, 17, 24, 42, 4, 20, 
    56, 45, 4, 12, 2, 48, 4, 62, 53, 50, 4, 50, 62, 53, 4, 45, 20, 56, 4, 15, 
    36, 58, 4, 14, 1, 61, 4, 53, 50, 62, 4, 30, 3, 63, 5, 52, 44, 1, 5, 23, 28, 
    5, 5, 21, 62, 13, 5, 25, 49, 14, 5, 29, 59, 20, 5, 62, 13, 21, 5, 28, 5, 
    23, 5, 49, 14, 25, 5, 5, 23, 28, 5, 59, 20, 29, 5, 35, 42, 30, 5, 45, 58, 
    33, 5, 42, 30, 35, 5, 55, 43, 38, 5, 30, 35, 42, 5, 38, 55, 43, 5, 1, 52, 
    44, 5, 58, 33, 45, 5, 14, 25, 49, 5, 44, 1, 52, 5, 43, 38, 55, 5, 33, 45, 
    58, 5, 20, 29, 59, 5, 13, 21, 62, 6, 46, 53, 0, 6, 43, 4, 3, 6, 3, 43, 4, 
    6, 54, 61, 7, 6, 60, 27, 8, 6, 41, 57, 9, 6, 18, 36, 10, 6, 58, 32, 12, 6, 
    22, 21, 16, 6, 36, 10, 18, 6, 16, 22, 21, 6, 21, 16, 22, 6, 8, 60, 27, 6, 
    12, 58, 32, 6, 10, 18, 36, 6, 57, 9, 41, 6, 4, 3, 43, 6, 53, 0, 46, 6, 0, 
    46, 53, 6, 61, 7, 54, 6, 9, 41, 57, 6, 32, 12, 58, 6, 27, 8, 60, 6, 7, 54, 
    61, 7, 3, 22, 0, 7, 22, 0, 3, 7, 24, 57, 4, 7, 59, 18, 5, 7, 51, 10, 6, 7, 
    55, 42, 7, 7, 33, 60, 8, 7, 6, 51, 10, 7, 5, 59, 18, 7, 39, 32, 19, 7, 0, 
    3, 22, 7, 57, 4, 24, 7, 56, 52, 28, 7, 19, 39, 32, 7, 60, 8, 33, 7, 32, 19, 
    39, 7, 7, 55, 42, 7, 10, 6, 51, 7, 28, 56, 52, 7, 42, 7, 55, 7, 52, 28, 56, 
    7, 4, 24, 57, 7, 18, 5, 59, 7, 8, 33, 60, 8, 19, 8, 0, 8, 25, 59, 4, 8, 33, 
    22, 6, 8, 56, 16, 7, 8, 0, 19, 8, 8, 39, 41, 13, 8, 35, 52, 15, 8, 7, 56, 
    16, 8, 36, 27, 18, 8, 8, 0, 19, 8, 57, 26, 21, 8, 6, 33, 22, 8, 59, 4, 25, 
    8, 21, 57, 26, 8, 18, 36, 27, 8, 22, 6, 33, 8, 52, 15, 35, 8, 27, 18, 36, 
    8, 41, 13, 39, 8, 13, 39, 41, 8, 15, 35, 52, 8, 16, 7, 56, 8, 26, 21, 57, 
    8, 4, 25, 59]));

