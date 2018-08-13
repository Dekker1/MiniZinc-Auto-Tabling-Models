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
data =[| 30, 23, 35, 29, 62, 37, 52, 40, 10, 18, 43, 17, 41,  7, 48, 54, 46, 16, 56, 33, 27,  0, 15, 59 |
   37, 53, 47, 32, 57, 16, 48, 30, 62, 58, 10, 55,  7, 14, 13, 36, 34, 60, 43, 49, 19, 29,  1, 56 |
   61, 53, 10, 11, 50, 41, 51,  4,  5, 28, 20, 18, 33, 40,  6, 16, 12, 56,  3,  8, 49, 14, 22, 15 |
   25, 29, 19,  4, 63, 30, 50, 47,  2, 53, 38, 51, 62, 60, 55, 39, 34, 12,  3, 15, 61, 24, 46, 42 |
   13, 50, 46, 38, 24,  8, 52, 31,  6, 41, 33,  3, 54, 59, 21, 28, 40, 37, 25, 36, 17,  9, 44, 42 |
   14, 60,  9, 58, 20,  1, 43, 38, 31, 57, 61,  6, 22, 11, 36, 63, 39, 24, 42, 34, 21, 49, 26, 45 |
   35, 47, 45, 11, 22,  7, 13, 28, 51,  0, 20, 27, 19, 63,  5, 44, 52, 25,  8, 31, 23,  2, 26, 32 |
    4, 32, 12, 57, 54, 23, 18,  2, 21,  5,  0, 44, 17,  9, 45, 55, 58,  1, 35, 39, 59, 26, 48, 27 |]
;
% cubes: [6, 5, 7, 3, 8, 1, 2, 4]
% symbols: [14, 24, 35, 53, 55, 48, 57, 62, 1, 21, 44, 40, 23, 62, 58, 3, 63, 41, 7, 8, 4, 18, 13, 2]
% rotations: [5, 10, 5, 6, 13, 14, 10, 15]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 40, 35, 0, 1, 33, 23, 7, 
    1, 56, 41, 10, 1, 46, 43, 15, 1, 59, 29, 16, 1, 52, 27, 17, 1, 48, 62, 18, 
    1, 7, 33, 23, 1, 17, 52, 27, 1, 16, 59, 29, 1, 37, 54, 30, 1, 23, 7, 33, 1, 
    0, 40, 35, 1, 54, 30, 37, 1, 35, 0, 40, 1, 10, 56, 41, 1, 15, 46, 43, 1, 
    43, 15, 46, 1, 62, 18, 48, 1, 27, 17, 52, 1, 30, 37, 54, 1, 41, 10, 56, 1, 
    29, 16, 59, 1, 18, 48, 62, 2, 34, 10, 1, 2, 62, 43, 7, 2, 1, 34, 10, 2, 57, 
    58, 13, 2, 49, 53, 14, 2, 36, 37, 16, 2, 55, 48, 19, 2, 30, 47, 29, 2, 47, 
    29, 30, 2, 60, 56, 32, 2, 10, 1, 34, 2, 37, 16, 36, 2, 16, 36, 37, 2, 7, 
    62, 43, 2, 29, 30, 47, 2, 19, 55, 48, 2, 53, 14, 49, 2, 14, 49, 53, 2, 48, 
    19, 55, 2, 32, 60, 56, 2, 58, 13, 57, 2, 13, 57, 58, 2, 56, 32, 60, 2, 43, 
    7, 62, 3, 33, 5, 3, 3, 10, 14, 4, 3, 3, 33, 5, 3, 50, 28, 6, 3, 53, 40, 8, 
    3, 14, 4, 10, 3, 56, 15, 11, 3, 20, 22, 12, 3, 4, 10, 14, 3, 11, 56, 15, 3, 
    61, 41, 16, 3, 51, 49, 18, 3, 22, 12, 20, 3, 12, 20, 22, 3, 6, 50, 28, 3, 
    5, 3, 33, 3, 8, 53, 40, 3, 16, 61, 41, 3, 18, 51, 49, 3, 28, 6, 50, 3, 49, 
    18, 51, 3, 40, 8, 53, 3, 15, 11, 56, 3, 41, 16, 61, 4, 3, 62, 2, 4, 62, 2, 
    3, 4, 12, 42, 4, 4, 42, 4, 12, 4, 29, 60, 15, 4, 24, 47, 19, 4, 47, 19, 24, 
    4, 30, 39, 25, 4, 60, 15, 29, 4, 39, 25, 30, 4, 38, 46, 34, 4, 46, 34, 38, 
    4, 25, 30, 39, 4, 4, 12, 42, 4, 34, 38, 46, 4, 19, 24, 47, 4, 61, 51, 50, 
    4, 50, 61, 51, 4, 55, 63, 53, 4, 63, 53, 55, 4, 15, 29, 60, 4, 51, 50, 61, 
    4, 2, 3, 62, 4, 53, 55, 63, 5, 52, 17, 3, 5, 25, 54, 6, 5, 28, 13, 8, 5, 
    31, 46, 9, 5, 8, 28, 13, 5, 3, 52, 17, 5, 24, 41, 21, 5, 41, 21, 24, 5, 54, 
    6, 25, 5, 13, 8, 28, 5, 46, 9, 31, 5, 44, 40, 33, 5, 50, 59, 36, 5, 42, 38, 
    37, 5, 37, 42, 38, 5, 33, 44, 40, 5, 21, 24, 41, 5, 38, 37, 42, 5, 40, 33, 
    44, 5, 9, 31, 46, 5, 59, 36, 50, 5, 17, 3, 52, 5, 6, 25, 54, 5, 36, 50, 59, 
    6, 63, 14, 1, 6, 43, 21, 6, 6, 49, 38, 9, 6, 34, 60, 11, 6, 1, 63, 14, 6, 
    57, 36, 20, 6, 6, 43, 21, 6, 31, 42, 22, 6, 45, 58, 24, 6, 39, 61, 26, 6, 
    42, 22, 31, 6, 60, 11, 34, 6, 20, 57, 36, 6, 9, 49, 38, 6, 61, 26, 39, 6, 
    22, 31, 42, 6, 21, 6, 43, 6, 58, 24, 45, 6, 38, 9, 49, 6, 36, 20, 57, 6, 
    24, 45, 58, 6, 11, 34, 60, 6, 26, 39, 61, 6, 14, 1, 63, 7, 5, 22, 0, 7, 28, 
    45, 2, 7, 22, 0, 5, 7, 44, 35, 7, 7, 19, 51, 8, 7, 25, 32, 11, 7, 23, 27, 
    13, 7, 51, 8, 19, 7, 26, 52, 20, 7, 0, 5, 22, 7, 27, 13, 23, 7, 32, 11, 25, 
    7, 52, 20, 26, 7, 13, 23, 27, 7, 45, 2, 28, 7, 47, 63, 31, 7, 11, 25, 32, 
    7, 7, 44, 35, 7, 35, 7, 44, 7, 2, 28, 45, 7, 63, 31, 47, 7, 8, 19, 51, 7, 
    20, 26, 52, 7, 31, 47, 63, 8, 48, 58, 0, 8, 27, 57, 1, 8, 12, 26, 2, 8, 23, 
    55, 4, 8, 45, 54, 5, 8, 39, 32, 9, 8, 26, 2, 12, 8, 21, 35, 17, 8, 59, 44, 
    18, 8, 35, 17, 21, 8, 55, 4, 23, 8, 2, 12, 26, 8, 57, 1, 27, 8, 9, 39, 32, 
    8, 17, 21, 35, 8, 32, 9, 39, 8, 18, 59, 44, 8, 54, 5, 45, 8, 58, 0, 48, 8, 
    5, 45, 54, 8, 4, 23, 55, 8, 1, 27, 57, 8, 0, 48, 58, 8, 44, 18, 59]));

