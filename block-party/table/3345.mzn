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
data =[| 56, 29, 24, 47, 38, 15, 50, 10, 63, 30, 40, 41, 39, 62,  2, 33, 34, 36, 54,  5, 25,  7, 55, 48 |
   27, 39, 35, 46,  8,  7, 21, 54, 18, 15, 25,  1, 29, 40, 38, 63, 32, 41, 62, 16, 53, 60, 17, 52 |
   20, 25, 43, 54, 10, 50, 57, 16, 39,  7, 63, 38, 31, 36, 42, 47,  5, 33,  2,  0, 48, 56, 11,  1 |
   21, 17, 41, 11, 58, 46,  9, 47, 51, 29, 60, 33, 26, 37,  1, 31, 23,  4, 10,  6, 12,  8, 28, 45 |
   28, 19, 42,  4, 43, 26, 57, 14,  2, 34, 13, 27, 59, 61, 36, 11, 23, 50,  5, 24, 45, 40, 32, 30 |
    4, 35, 12, 59, 61, 27, 24, 26,  3, 20, 34, 18, 13,  6, 48, 51, 58, 44, 53, 57, 45, 37, 22, 49 |
   52,  8, 56,  9, 13, 22, 16, 43, 23,  6, 18, 19, 55, 62, 49, 35,  3, 42, 14, 12, 37, 53, 44,  0 |
   49, 51, 30, 15, 20, 31, 14, 52, 61,  9, 44,  0, 55, 46, 32, 21, 28, 17, 60, 58, 59, 22, 19,  3 |]
;
% cubes: [5, 3, 6, 1, 7, 8, 4, 2]
% symbols: [2, 38, 26, 62, 43, 51, 31, 7, 5, 48, 37, 5, 53, 46, 21, 27, 59, 57, 12, 29, 56, 58, 46, 63]
% rotations: [23, 21, 12, 16, 12, 6, 13, 11]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 38, 30, 2, 1, 29, 62, 5, 
    1, 10, 24, 7, 1, 24, 7, 10, 1, 33, 56, 15, 1, 7, 10, 24, 1, 41, 50, 25, 1, 
    62, 5, 29, 1, 2, 38, 30, 1, 56, 15, 33, 1, 40, 55, 34, 1, 48, 47, 36, 1, 
    30, 2, 38, 1, 63, 54, 39, 1, 55, 34, 40, 1, 50, 25, 41, 1, 36, 48, 47, 1, 
    47, 36, 48, 1, 25, 41, 50, 1, 39, 63, 54, 1, 34, 40, 55, 1, 15, 33, 56, 1, 
    5, 29, 62, 1, 54, 39, 63, 2, 21, 53, 1, 2, 63, 27, 7, 2, 15, 38, 8, 2, 38, 
    8, 15, 2, 39, 40, 16, 2, 32, 25, 17, 2, 62, 29, 18, 2, 53, 1, 21, 2, 17, 
    32, 25, 2, 7, 63, 27, 2, 18, 62, 29, 2, 25, 17, 32, 2, 60, 54, 35, 2, 8, 
    15, 38, 2, 40, 16, 39, 2, 16, 39, 40, 2, 52, 46, 41, 2, 41, 52, 46, 2, 46, 
    41, 52, 2, 1, 21, 53, 2, 35, 60, 54, 2, 54, 35, 60, 2, 29, 18, 62, 2, 27, 
    7, 63, 3, 25, 36, 0, 3, 54, 33, 1, 3, 31, 39, 2, 3, 63, 11, 5, 3, 42, 10, 
    7, 3, 7, 42, 10, 3, 5, 63, 11, 3, 43, 56, 16, 3, 50, 47, 20, 3, 36, 0, 25, 
    3, 39, 2, 31, 3, 1, 54, 33, 3, 0, 25, 36, 3, 57, 48, 38, 3, 2, 31, 39, 3, 
    10, 7, 42, 3, 56, 16, 43, 3, 20, 50, 47, 3, 38, 57, 48, 3, 47, 20, 50, 3, 
    33, 1, 54, 3, 16, 43, 56, 3, 48, 38, 57, 3, 11, 5, 63, 4, 58, 29, 1, 4, 45, 
    11, 4, 4, 17, 37, 6, 4, 47, 41, 8, 4, 12, 33, 9, 4, 26, 51, 10, 4, 4, 45, 
    11, 4, 33, 9, 12, 4, 37, 6, 17, 4, 46, 31, 21, 4, 60, 28, 23, 4, 51, 10, 
    26, 4, 23, 60, 28, 4, 1, 58, 29, 4, 21, 46, 31, 4, 9, 12, 33, 4, 6, 17, 37, 
    4, 8, 47, 41, 4, 11, 4, 45, 4, 31, 21, 46, 4, 41, 8, 47, 4, 10, 26, 51, 4, 
    29, 1, 58, 4, 28, 23, 60, 5, 5, 59, 2, 5, 50, 30, 4, 5, 59, 2, 5, 5, 28, 
    26, 11, 5, 32, 23, 13, 5, 42, 40, 14, 5, 61, 24, 19, 5, 13, 32, 23, 5, 19, 
    61, 24, 5, 11, 28, 26, 5, 57, 45, 27, 5, 26, 11, 28, 5, 4, 50, 30, 5, 23, 
    13, 32, 5, 36, 43, 34, 5, 43, 34, 36, 5, 14, 42, 40, 5, 40, 14, 42, 5, 34, 
    36, 43, 5, 27, 57, 45, 5, 30, 4, 50, 5, 45, 27, 57, 5, 2, 5, 59, 5, 24, 19, 
    61, 6, 53, 13, 3, 6, 27, 51, 4, 6, 57, 35, 6, 6, 37, 26, 12, 6, 3, 53, 13, 
    6, 24, 45, 18, 6, 48, 61, 20, 6, 58, 34, 22, 6, 45, 18, 24, 6, 12, 37, 26, 
    6, 51, 4, 27, 6, 22, 58, 34, 6, 6, 57, 35, 6, 26, 12, 37, 6, 49, 59, 44, 6, 
    18, 24, 45, 6, 61, 20, 48, 6, 59, 44, 49, 6, 4, 27, 51, 6, 13, 3, 53, 6, 
    35, 6, 57, 6, 34, 22, 58, 6, 44, 49, 59, 6, 20, 48, 61, 7, 9, 42, 0, 7, 18, 
    44, 3, 7, 49, 13, 6, 7, 62, 12, 8, 7, 42, 0, 9, 7, 8, 62, 12, 7, 6, 49, 13, 
    7, 55, 23, 14, 7, 37, 19, 16, 7, 44, 3, 18, 7, 16, 37, 19, 7, 35, 52, 22, 
    7, 14, 55, 23, 7, 52, 22, 35, 7, 19, 16, 37, 7, 0, 9, 42, 7, 56, 53, 43, 7, 
    3, 18, 44, 7, 13, 6, 49, 7, 22, 35, 52, 7, 43, 56, 53, 7, 23, 14, 55, 7, 
    53, 43, 56, 7, 12, 8, 62, 8, 14, 59, 0, 8, 15, 17, 3, 8, 32, 20, 9, 8, 59, 
    0, 14, 8, 17, 3, 15, 8, 3, 15, 17, 8, 28, 44, 19, 8, 9, 32, 20, 8, 49, 31, 
    21, 8, 52, 30, 22, 8, 44, 19, 28, 8, 22, 52, 30, 8, 21, 49, 31, 8, 20, 9, 
    32, 8, 19, 28, 44, 8, 58, 51, 46, 8, 31, 21, 49, 8, 46, 58, 51, 8, 30, 22, 
    52, 8, 61, 60, 55, 8, 51, 46, 58, 8, 0, 14, 59, 8, 55, 61, 60, 8, 60, 55, 
    61]));

