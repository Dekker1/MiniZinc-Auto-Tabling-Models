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
data =[| 15, 39, 57, 20, 61, 36, 41, 22, 47, 43, 29,  6, 14, 17, 18, 40, 54, 34, 42,  3, 24, 13, 10, 30 |
   15, 45, 20, 19, 47, 57,  7, 46, 59, 14, 56, 17, 11, 34, 37, 62, 55, 54, 61, 16,  9, 31, 51,  2 |
   45, 17, 18, 26, 29, 11, 57, 46, 23, 22, 49, 24, 20, 53, 35, 28, 19, 38,  4,  3,  0, 52,  8,  9 |
   52, 51, 14,  2,  3, 45, 44, 16, 43, 39, 37, 21, 58,  0, 28, 36, 38,  7, 33,  1, 32, 63, 61,  6 |
   60, 36, 24, 15, 48, 23, 47,  9,  0, 10, 32, 28, 41, 46,  2, 33, 35, 25, 12, 55,  4, 44, 40, 29 |
    7, 63, 34, 16, 25, 44, 21, 39,  6,  5, 33, 30, 22, 26, 55, 41, 32, 31, 11, 18, 48, 42, 50, 27 |
   38, 63, 52, 31, 56, 49, 10, 59, 48, 19, 37,  1, 62,  8, 58, 43, 25,  5, 60, 12, 27, 50, 53, 13 |
   35,  4, 60, 13, 49,  8, 59, 21, 56, 62, 30,  1,  5, 23, 54, 40, 58, 50, 42, 53, 27, 26, 51, 12 |]
;
% cubes: [1, 2, 8, 3, 6, 7, 5, 4]
% symbols: [41, 19, 62, 4, 11, 49, 28, 38, 24, 2, 49, 20, 6, 43, 47, 61, 6, 54, 54, 23, 22, 38, 4, 37]
% rotations: [9, 7, 24, 19, 19, 11, 21, 20]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 39, 17, 3, 1, 41, 24, 6, 
    1, 54, 29, 10, 1, 22, 57, 13, 1, 47, 42, 14, 1, 36, 40, 15, 1, 3, 39, 17, 
    1, 61, 43, 18, 1, 34, 30, 20, 1, 57, 13, 22, 1, 6, 41, 24, 1, 10, 54, 29, 
    1, 20, 34, 30, 1, 30, 20, 34, 1, 40, 15, 36, 1, 17, 3, 39, 1, 15, 36, 40, 
    1, 24, 6, 41, 1, 14, 47, 42, 1, 18, 61, 43, 1, 42, 14, 47, 1, 29, 10, 54, 
    1, 13, 22, 57, 1, 43, 18, 61, 2, 19, 54, 2, 2, 9, 17, 7, 2, 17, 7, 9, 2, 
    59, 61, 11, 2, 37, 47, 14, 2, 57, 62, 15, 2, 45, 34, 16, 2, 7, 9, 17, 2, 
    54, 2, 19, 2, 31, 46, 20, 2, 46, 20, 31, 2, 16, 45, 34, 2, 47, 14, 37, 2, 
    34, 16, 45, 2, 20, 31, 46, 2, 14, 37, 47, 2, 55, 56, 51, 2, 2, 19, 54, 2, 
    56, 51, 55, 2, 51, 55, 56, 2, 62, 15, 57, 2, 61, 11, 59, 2, 11, 59, 61, 2, 
    15, 57, 62, 3, 24, 57, 0, 3, 17, 53, 3, 3, 20, 23, 4, 3, 19, 49, 8, 3, 26, 
    38, 9, 3, 28, 45, 11, 3, 53, 3, 17, 3, 52, 46, 18, 3, 49, 8, 19, 3, 23, 4, 
    20, 3, 35, 29, 22, 3, 4, 20, 23, 3, 57, 0, 24, 3, 38, 9, 26, 3, 45, 11, 28, 
    3, 22, 35, 29, 3, 29, 22, 35, 3, 9, 26, 38, 3, 11, 28, 45, 3, 18, 52, 46, 
    3, 8, 19, 49, 3, 46, 18, 52, 3, 3, 17, 53, 3, 0, 24, 57, 4, 1, 51, 0, 4, 
    51, 0, 1, 4, 7, 6, 2, 4, 39, 28, 3, 4, 2, 7, 6, 4, 6, 2, 7, 4, 63, 16, 14, 
    4, 14, 63, 16, 4, 44, 32, 21, 4, 3, 39, 28, 4, 21, 44, 32, 4, 58, 43, 33, 
    4, 52, 45, 36, 4, 61, 38, 37, 4, 37, 61, 38, 4, 28, 3, 39, 4, 33, 58, 43, 
    4, 32, 21, 44, 4, 36, 52, 45, 4, 0, 1, 51, 4, 45, 36, 52, 4, 43, 33, 58, 4, 
    38, 37, 61, 4, 16, 14, 63, 5, 12, 41, 0, 5, 48, 10, 2, 5, 28, 47, 4, 5, 24, 
    44, 9, 5, 2, 48, 10, 5, 41, 0, 12, 5, 25, 29, 15, 5, 33, 60, 23, 5, 44, 9, 
    24, 5, 29, 15, 25, 5, 47, 4, 28, 5, 15, 25, 29, 5, 40, 35, 32, 5, 60, 23, 
    33, 5, 32, 40, 35, 5, 46, 55, 36, 5, 35, 32, 40, 5, 0, 12, 41, 5, 9, 24, 
    44, 5, 55, 36, 46, 5, 4, 28, 47, 5, 10, 2, 48, 5, 36, 46, 55, 5, 23, 33, 
    60, 6, 55, 25, 5, 6, 11, 22, 6, 6, 44, 41, 7, 6, 22, 6, 11, 6, 31, 27, 16, 
    6, 63, 26, 18, 6, 48, 30, 21, 6, 6, 11, 22, 6, 5, 55, 25, 6, 18, 63, 26, 6, 
    16, 31, 27, 6, 21, 48, 30, 6, 27, 16, 31, 6, 33, 50, 32, 6, 50, 32, 33, 6, 
    42, 39, 34, 6, 34, 42, 39, 6, 7, 44, 41, 6, 39, 34, 42, 6, 41, 7, 44, 6, 
    30, 21, 48, 6, 32, 33, 50, 6, 25, 5, 55, 6, 26, 18, 63, 7, 10, 27, 1, 7, 
    13, 31, 5, 7, 12, 63, 8, 7, 27, 1, 10, 7, 63, 8, 12, 7, 31, 5, 13, 7, 58, 
    56, 19, 7, 37, 53, 25, 7, 1, 10, 27, 7, 5, 13, 31, 7, 53, 25, 37, 7, 49, 
    43, 38, 7, 38, 49, 43, 7, 60, 62, 48, 7, 43, 38, 49, 7, 59, 52, 50, 7, 50, 
    59, 52, 7, 25, 37, 53, 7, 19, 58, 56, 7, 56, 19, 58, 7, 52, 50, 59, 7, 62, 
    48, 60, 7, 48, 60, 62, 7, 8, 12, 63, 8, 59, 27, 1, 8, 23, 53, 4, 8, 56, 42, 
    5, 8, 40, 35, 8, 8, 13, 50, 12, 8, 50, 12, 13, 8, 60, 26, 21, 8, 53, 4, 23, 
    8, 21, 60, 26, 8, 1, 59, 27, 8, 51, 58, 30, 8, 8, 40, 35, 8, 35, 8, 40, 8, 
    5, 56, 42, 8, 62, 54, 49, 8, 12, 13, 50, 8, 58, 30, 51, 8, 4, 23, 53, 8, 
    49, 62, 54, 8, 42, 5, 56, 8, 30, 51, 58, 8, 27, 1, 59, 8, 26, 21, 60, 8, 
    54, 49, 62]));

