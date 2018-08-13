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
data =[| 52, 29, 10, 60, 23, 24,  7, 31, 48, 47,  1, 26, 37, 22, 61,  5, 58, 27, 25, 28,  2, 40, 21, 14 |
   45, 22, 36,  9, 51, 53, 44,  5, 30, 49, 46, 57, 43, 23, 60, 29, 18, 34, 27, 14, 61, 59, 41,  1 |
   53, 13,  5, 20, 63, 24, 60, 59, 31, 51, 56, 49, 22, 12, 28, 47, 40, 52, 27, 39, 26, 43, 54, 57 |
   13, 41, 39,  8, 33, 35, 46, 55,  0, 24, 62, 61, 54, 34, 20, 50, 51,  6, 63, 52,  1, 18, 21, 11 |
   37, 18, 33,  9, 30, 56, 50,  8,  4, 42, 23, 13, 43, 45, 21,  0, 12, 41, 20, 63, 28, 38, 36,  7 |
   49, 34,  0, 56, 47, 57, 26, 54, 35, 32,  3, 29, 10, 39, 19, 58, 59,  9,  2, 17, 36,  8, 15, 16 |
   58, 19, 53,  3, 62, 12, 55, 32, 42, 48,  6, 15, 16, 50, 30, 35, 33, 17,  4, 25, 11,  2, 38, 44 |
   14, 48, 42,  3, 55, 25,  4, 11, 38, 37, 44, 19, 46, 31, 16, 15, 32,  7,  6, 45, 17, 10, 40, 62 |]
;
% cubes: [4, 3, 7, 6, 2, 5, 1, 8]
% symbols: [46, 22, 2, 58, 18, 23, 28, 25, 1, 27, 53, 49, 41, 36, 29, 14, 61, 31, 32, 57, 46, 12, 22, 15]
% rotations: [9, 15, 4, 13, 20, 22, 18, 11]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 21, 58, 1, 1, 26, 7, 2, 1, 
    52, 24, 5, 1, 2, 26, 7, 1, 40, 31, 10, 1, 60, 27, 14, 1, 58, 1, 21, 1, 28, 
    29, 22, 1, 47, 61, 23, 1, 5, 52, 24, 1, 37, 48, 25, 1, 7, 2, 26, 1, 14, 60, 
    27, 1, 29, 22, 28, 1, 22, 28, 29, 1, 10, 40, 31, 1, 48, 25, 37, 1, 31, 10, 
    40, 1, 61, 23, 47, 1, 25, 37, 48, 1, 24, 5, 52, 1, 1, 21, 58, 1, 27, 14, 
    60, 1, 23, 47, 61, 2, 9, 34, 1, 2, 36, 59, 5, 2, 34, 1, 9, 2, 22, 23, 14, 
    2, 46, 41, 18, 2, 23, 14, 22, 2, 14, 22, 23, 2, 43, 30, 27, 2, 45, 53, 29, 
    2, 27, 43, 30, 2, 1, 9, 34, 2, 59, 5, 36, 2, 18, 46, 41, 2, 30, 27, 43, 2, 
    61, 57, 44, 2, 53, 29, 45, 2, 41, 18, 46, 2, 60, 51, 49, 2, 49, 60, 51, 2, 
    29, 45, 53, 2, 44, 61, 57, 2, 5, 36, 59, 2, 51, 49, 60, 2, 57, 44, 61, 3, 
    43, 59, 5, 3, 39, 13, 12, 3, 12, 39, 13, 3, 52, 57, 20, 3, 31, 27, 22, 3, 
    47, 53, 24, 3, 49, 60, 26, 3, 22, 31, 27, 3, 63, 51, 28, 3, 27, 22, 31, 3, 
    13, 12, 39, 3, 56, 54, 40, 3, 59, 5, 43, 3, 53, 24, 47, 3, 60, 26, 49, 3, 
    28, 63, 51, 3, 57, 20, 52, 3, 24, 47, 53, 3, 40, 56, 54, 3, 54, 40, 56, 3, 
    20, 52, 57, 3, 5, 43, 59, 3, 26, 49, 60, 3, 51, 28, 63, 4, 63, 54, 0, 4, 
    61, 46, 1, 4, 11, 8, 6, 4, 6, 11, 8, 4, 8, 6, 11, 4, 35, 50, 13, 4, 55, 39, 
    18, 4, 33, 24, 20, 4, 51, 62, 21, 4, 20, 33, 24, 4, 24, 20, 33, 4, 52, 41, 
    34, 4, 50, 13, 35, 4, 18, 55, 39, 4, 34, 52, 41, 4, 1, 61, 46, 4, 13, 35, 
    50, 4, 62, 21, 51, 4, 41, 34, 52, 4, 0, 63, 54, 4, 39, 18, 55, 4, 46, 1, 
    61, 4, 21, 51, 62, 4, 54, 0, 63, 5, 37, 56, 0, 5, 20, 43, 4, 5, 9, 41, 7, 
    5, 33, 38, 8, 5, 41, 7, 9, 5, 23, 36, 12, 5, 50, 28, 13, 5, 45, 63, 18, 5, 
    43, 4, 20, 5, 30, 42, 21, 5, 36, 12, 23, 5, 13, 50, 28, 5, 42, 21, 30, 5, 
    38, 8, 33, 5, 12, 23, 36, 5, 56, 0, 37, 5, 8, 33, 38, 5, 7, 9, 41, 5, 21, 
    30, 42, 5, 4, 20, 43, 5, 63, 18, 45, 5, 28, 13, 50, 5, 0, 37, 56, 5, 18, 
    45, 63, 6, 8, 54, 0, 6, 10, 35, 2, 6, 15, 59, 3, 6, 54, 0, 8, 6, 16, 56, 9, 
    6, 35, 2, 10, 6, 59, 3, 15, 6, 56, 9, 16, 6, 34, 39, 17, 6, 47, 32, 19, 6, 
    36, 29, 26, 6, 26, 36, 29, 6, 19, 47, 32, 6, 39, 17, 34, 6, 2, 10, 35, 6, 
    29, 26, 36, 6, 17, 34, 39, 6, 32, 19, 47, 6, 57, 58, 49, 6, 0, 8, 54, 6, 9, 
    16, 56, 6, 58, 49, 57, 6, 49, 57, 58, 6, 3, 15, 59, 7, 32, 53, 2, 7, 17, 
    44, 3, 7, 16, 42, 4, 7, 38, 33, 6, 7, 15, 55, 11, 7, 35, 58, 12, 7, 55, 11, 
    15, 7, 42, 4, 16, 7, 44, 3, 17, 7, 50, 25, 19, 7, 19, 50, 25, 7, 62, 48, 
    30, 7, 53, 2, 32, 7, 6, 38, 33, 7, 58, 12, 35, 7, 33, 6, 38, 7, 4, 16, 42, 
    7, 3, 17, 44, 7, 30, 62, 48, 7, 25, 19, 50, 7, 2, 32, 53, 7, 11, 15, 55, 7, 
    12, 35, 58, 7, 48, 30, 62, 8, 7, 62, 3, 8, 17, 19, 4, 8, 46, 38, 6, 8, 62, 
    3, 7, 8, 11, 42, 10, 8, 42, 10, 11, 8, 25, 15, 14, 8, 14, 25, 15, 8, 55, 
    37, 16, 8, 19, 4, 17, 8, 4, 17, 19, 8, 15, 14, 25, 8, 45, 48, 31, 8, 44, 
    40, 32, 8, 16, 55, 37, 8, 6, 46, 38, 8, 32, 44, 40, 8, 10, 11, 42, 8, 40, 
    32, 44, 8, 48, 31, 45, 8, 38, 6, 46, 8, 31, 45, 48, 8, 37, 16, 55, 8, 3, 7, 
    62]));

