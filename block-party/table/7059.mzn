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
data =[| 56, 42, 49,  5, 34, 14, 40, 45, 62, 18, 12, 51, 50, 39, 26, 25, 28, 10, 11, 63, 32, 61, 19, 58 |
   17, 51,  3,  7, 25, 46, 29, 41, 57, 48, 53, 20, 56, 15, 22, 12, 60, 38, 33, 34, 27, 14, 55, 40 |
   61, 18, 23, 44, 32,  6, 52, 51, 29,  2, 22, 56,  0, 14, 19, 46,  9, 60, 40, 17,  3, 48, 50, 37 |
   47, 49, 28, 63, 27, 21,  1, 25, 45, 55,  3, 42, 54, 61, 53, 34, 48, 43,  6, 39, 29, 52,  4, 33 |
   50, 13, 38,  7, 15, 36, 21, 10, 42, 12, 23, 16, 55, 27, 45, 60, 35, 53, 44, 26, 46, 22,  0, 52 |
   36,  1, 15, 58, 37, 35,  7,  0, 21,  4, 33,  8, 19, 44, 62, 16, 17, 32, 26, 59, 30, 31, 24, 39 |
   47, 31, 38, 35, 43,  8, 62, 16, 36,  1, 41, 23, 59, 57, 49, 30,  2,  5, 24, 11, 13, 20,  9, 54 |
   57, 18, 20,  5, 28,  4, 13, 63, 30, 43,  2, 24,  8, 10, 59, 37, 41, 11,  9,  6, 47, 58, 31, 54 |]
;
% cubes: [6, 7, 8, 1, 4, 5, 3, 2]
% symbols: [39, 49, 10, 28, 54, 22, 6, 38, 58, 1, 18, 12, 6, 10, 46, 7, 32, 43, 6, 19, 45, 38, 61, 40]
% rotations: [3, 14, 16, 20, 15, 4, 11, 17]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 10, 58, 5, 1, 58, 5, 10, 
    1, 50, 62, 11, 1, 19, 28, 12, 1, 25, 56, 14, 1, 26, 34, 18, 1, 28, 12, 19, 
    1, 56, 14, 25, 1, 34, 18, 26, 1, 12, 19, 28, 1, 51, 40, 32, 1, 18, 26, 34, 
    1, 63, 42, 39, 1, 32, 51, 40, 1, 39, 63, 42, 1, 49, 61, 45, 1, 61, 45, 49, 
    1, 62, 11, 50, 1, 40, 32, 51, 1, 14, 25, 56, 1, 5, 10, 58, 1, 45, 49, 61, 
    1, 11, 50, 62, 1, 42, 39, 63, 2, 14, 41, 3, 2, 38, 40, 7, 2, 17, 46, 12, 2, 
    41, 3, 14, 2, 34, 51, 15, 2, 46, 12, 17, 2, 29, 27, 20, 2, 25, 48, 22, 2, 
    48, 22, 25, 2, 20, 29, 27, 2, 27, 20, 29, 2, 56, 57, 33, 2, 51, 15, 34, 2, 
    40, 7, 38, 2, 7, 38, 40, 2, 3, 14, 41, 2, 12, 17, 46, 2, 22, 25, 48, 2, 15, 
    34, 51, 2, 55, 60, 53, 2, 60, 53, 55, 2, 57, 33, 56, 2, 33, 56, 57, 2, 53, 
    55, 60, 3, 29, 40, 0, 3, 19, 32, 2, 3, 56, 52, 3, 3, 46, 61, 6, 3, 22, 50, 
    9, 3, 17, 18, 14, 3, 18, 14, 17, 3, 14, 17, 18, 3, 32, 2, 19, 3, 50, 9, 22, 
    3, 48, 51, 23, 3, 40, 0, 29, 3, 2, 19, 32, 3, 44, 60, 37, 3, 0, 29, 40, 3, 
    60, 37, 44, 3, 61, 6, 46, 3, 51, 23, 48, 3, 9, 22, 50, 3, 23, 48, 51, 3, 3, 
    56, 52, 3, 52, 3, 56, 3, 37, 44, 60, 3, 6, 46, 61, 4, 29, 42, 1, 4, 4, 48, 
    3, 4, 48, 3, 4, 4, 54, 45, 6, 4, 34, 47, 21, 4, 28, 52, 25, 4, 55, 53, 27, 
    4, 52, 25, 28, 4, 42, 1, 29, 4, 63, 43, 33, 4, 47, 21, 34, 4, 49, 61, 39, 
    4, 1, 29, 42, 4, 33, 63, 43, 4, 6, 54, 45, 4, 21, 34, 47, 4, 3, 4, 48, 4, 
    61, 39, 49, 4, 25, 28, 52, 4, 27, 55, 53, 4, 45, 6, 54, 4, 53, 27, 55, 4, 
    39, 49, 61, 4, 43, 33, 63, 5, 35, 23, 0, 5, 53, 52, 7, 5, 38, 22, 10, 5, 
    45, 15, 12, 5, 27, 26, 13, 5, 12, 45, 15, 5, 21, 46, 16, 5, 46, 16, 21, 5, 
    10, 38, 22, 5, 0, 35, 23, 5, 13, 27, 26, 5, 26, 13, 27, 5, 23, 0, 35, 5, 
    60, 50, 36, 5, 22, 10, 38, 5, 44, 55, 42, 5, 55, 42, 44, 5, 15, 12, 45, 5, 
    16, 21, 46, 5, 36, 60, 50, 5, 7, 53, 52, 5, 52, 7, 53, 5, 42, 44, 55, 5, 
    50, 36, 60, 6, 15, 31, 0, 6, 44, 59, 1, 6, 62, 37, 4, 6, 30, 8, 7, 6, 7, 
    30, 8, 6, 31, 0, 15, 6, 36, 35, 16, 6, 33, 24, 17, 6, 21, 26, 19, 6, 26, 
    19, 21, 6, 17, 33, 24, 6, 19, 21, 26, 6, 8, 7, 30, 6, 0, 15, 31, 6, 39, 58, 
    32, 6, 24, 17, 33, 6, 16, 36, 35, 6, 35, 16, 36, 6, 4, 62, 37, 6, 58, 32, 
    39, 6, 59, 1, 44, 6, 32, 39, 58, 6, 1, 44, 59, 6, 37, 4, 62, 7, 49, 43, 1, 
    7, 41, 9, 2, 7, 54, 35, 5, 7, 30, 47, 8, 7, 2, 41, 9, 7, 31, 57, 11, 7, 23, 
    62, 13, 7, 38, 20, 16, 7, 16, 38, 20, 7, 62, 13, 23, 7, 59, 36, 24, 7, 47, 
    8, 30, 7, 57, 11, 31, 7, 5, 54, 35, 7, 24, 59, 36, 7, 20, 16, 38, 7, 9, 2, 
    41, 7, 1, 49, 43, 7, 8, 30, 47, 7, 43, 1, 49, 7, 35, 5, 54, 7, 11, 31, 57, 
    7, 36, 24, 59, 7, 13, 23, 62, 8, 31, 41, 2, 8, 37, 57, 4, 8, 11, 54, 5, 8, 
    18, 10, 6, 8, 30, 9, 8, 8, 8, 30, 9, 8, 6, 18, 10, 8, 54, 5, 11, 8, 47, 24, 
    13, 8, 10, 6, 18, 8, 58, 63, 20, 8, 13, 47, 24, 8, 43, 59, 28, 8, 9, 8, 30, 
    8, 41, 2, 31, 8, 57, 4, 37, 8, 2, 31, 41, 8, 59, 28, 43, 8, 24, 13, 47, 8, 
    5, 11, 54, 8, 4, 37, 57, 8, 63, 20, 58, 8, 28, 43, 59, 8, 20, 58, 63]));

