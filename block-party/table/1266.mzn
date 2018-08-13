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
data =[| 14,  2, 29, 16, 33,  3, 63, 47,  6, 26, 19, 34, 31, 44, 23,  9, 38, 49, 27,  7, 32, 37, 52, 17 |
   14, 47, 57, 53, 59, 37, 48, 41, 27, 12,  7, 52, 20, 44, 17, 21, 13, 43,  1, 10,  6, 23, 39,  9 |
    2, 27, 18, 10, 35, 53,  7, 33, 58, 57, 50, 30, 36, 31, 14,  4, 44, 12, 63, 49, 23, 52, 15, 19 |
   25, 34,  3, 40,  2, 33, 16, 43, 18, 31, 45, 21, 48, 10, 53, 24, 28, 59, 41,  4, 13, 57, 35, 63 |
   38, 18, 36, 26, 41, 60, 43, 22, 48, 28, 42, 46,  9, 20, 50, 56,  3, 37, 24, 17, 39,  8, 62, 45 |
   46,  0,  1, 16, 15, 25,  4, 19, 30, 34, 36, 13, 61, 51, 60, 40,  8, 26, 39, 11, 54,  5, 55, 62 |
   46, 29,  6, 30, 25, 59, 62, 35, 60, 28, 38, 11, 32,  5, 56, 42,  0, 54, 51, 22, 55,  1, 61, 58 |
   42, 32, 54, 21, 11, 49, 24, 15, 29, 58,  8, 51,  0, 55, 22, 50,  5, 45, 40, 12, 47, 61, 20, 56 |]
;
% cubes: [8, 3, 2, 7, 1, 6, 5, 4]
% symbols: [49, 33, 17, 1, 31, 16, 26, 21, 50, 52, 12, 35, 27, 26, 37, 13, 42, 18, 59, 6, 6, 62, 45, 16]
% rotations: [11, 12, 14, 4, 15, 7, 7, 21]

%% ---------- GENERATED TABLE ----------
include "table.mzn";

predicate link_cube_and_symbols(array [1..4] of var int: cs) = 
    table_int(cs, array2d(1..192, index_set(cs), [1, 44, 7, 2, 1, 9, 14, 3, 1, 
    27, 31, 6, 1, 2, 44, 7, 1, 14, 3, 9, 1, 3, 9, 14, 1, 49, 17, 16, 1, 16, 49, 
    17, 1, 52, 38, 19, 1, 33, 26, 23, 1, 23, 33, 26, 1, 31, 6, 27, 1, 37, 47, 
    29, 1, 6, 27, 31, 1, 34, 63, 32, 1, 26, 23, 33, 1, 63, 32, 34, 1, 47, 29, 
    37, 1, 19, 52, 38, 1, 7, 2, 44, 1, 29, 37, 47, 1, 17, 16, 49, 1, 38, 19, 
    52, 1, 32, 34, 63, 2, 20, 27, 1, 2, 52, 48, 6, 2, 39, 13, 7, 2, 53, 43, 9, 
    2, 47, 44, 10, 2, 17, 59, 12, 2, 7, 39, 13, 2, 37, 21, 14, 2, 59, 12, 17, 
    2, 27, 1, 20, 2, 14, 37, 21, 2, 41, 57, 23, 2, 1, 20, 27, 2, 21, 14, 37, 2, 
    13, 7, 39, 2, 57, 23, 41, 2, 9, 53, 43, 2, 10, 47, 44, 2, 44, 10, 47, 2, 6, 
    52, 48, 2, 48, 6, 52, 2, 43, 9, 53, 2, 23, 41, 57, 2, 12, 17, 59, 3, 53, 4, 
    2, 3, 2, 53, 4, 3, 23, 30, 7, 3, 12, 19, 10, 3, 19, 10, 12, 3, 35, 57, 14, 
    3, 44, 50, 15, 3, 52, 33, 18, 3, 10, 12, 19, 3, 30, 7, 23, 3, 31, 49, 27, 
    3, 7, 23, 30, 3, 49, 27, 31, 3, 18, 52, 33, 3, 57, 14, 35, 3, 58, 63, 36, 
    3, 50, 15, 44, 3, 27, 31, 49, 3, 15, 44, 50, 3, 33, 18, 52, 3, 4, 2, 53, 3, 
    14, 35, 57, 3, 63, 36, 58, 3, 36, 58, 63, 4, 31, 53, 2, 4, 57, 43, 3, 4, 
    34, 10, 4, 4, 4, 34, 10, 4, 21, 16, 13, 4, 13, 21, 16, 4, 41, 48, 18, 4, 
    16, 13, 21, 4, 25, 33, 24, 4, 33, 24, 25, 4, 45, 35, 28, 4, 53, 2, 31, 4, 
    24, 25, 33, 4, 10, 4, 34, 4, 28, 45, 35, 4, 59, 63, 40, 4, 48, 18, 41, 4, 
    3, 57, 43, 4, 35, 28, 45, 4, 18, 41, 48, 4, 2, 31, 53, 4, 43, 3, 57, 4, 63, 
    40, 59, 4, 40, 59, 63, 5, 42, 62, 3, 5, 22, 36, 8, 5, 48, 24, 9, 5, 18, 20, 
    17, 5, 20, 17, 18, 5, 17, 18, 20, 5, 36, 8, 22, 5, 9, 48, 24, 5, 37, 45, 
    26, 5, 50, 41, 28, 5, 8, 22, 36, 5, 45, 26, 37, 5, 60, 56, 38, 5, 46, 43, 
    39, 5, 28, 50, 41, 5, 62, 3, 42, 5, 39, 46, 43, 5, 26, 37, 45, 5, 43, 39, 
    46, 5, 24, 9, 48, 5, 41, 28, 50, 5, 38, 60, 56, 5, 56, 38, 60, 5, 3, 42, 
    62, 6, 51, 11, 0, 6, 5, 19, 1, 6, 54, 13, 4, 6, 19, 1, 5, 6, 36, 55, 8, 6, 
    0, 51, 11, 6, 4, 54, 13, 6, 34, 60, 15, 6, 26, 62, 16, 6, 1, 5, 19, 6, 40, 
    46, 25, 6, 62, 16, 26, 6, 39, 61, 30, 6, 60, 15, 34, 6, 55, 8, 36, 6, 61, 
    30, 39, 6, 46, 25, 40, 6, 25, 40, 46, 6, 11, 0, 51, 6, 13, 4, 54, 6, 8, 36, 
    55, 6, 15, 34, 60, 6, 30, 39, 61, 6, 16, 26, 62, 7, 38, 61, 0, 7, 35, 6, 1, 
    7, 22, 29, 5, 7, 1, 35, 6, 7, 62, 55, 11, 7, 29, 5, 22, 7, 28, 56, 25, 7, 
    56, 25, 28, 7, 5, 22, 29, 7, 54, 58, 30, 7, 60, 51, 32, 7, 6, 1, 35, 7, 61, 
    0, 38, 7, 46, 59, 42, 7, 59, 42, 46, 7, 32, 60, 51, 7, 58, 30, 54, 7, 11, 
    62, 55, 7, 25, 28, 56, 7, 30, 54, 58, 7, 42, 46, 59, 7, 51, 32, 60, 7, 0, 
    38, 61, 7, 55, 11, 62, 8, 29, 40, 0, 8, 8, 20, 5, 8, 20, 5, 8, 8, 58, 22, 
    11, 8, 32, 55, 12, 8, 54, 61, 15, 8, 5, 8, 20, 8, 45, 56, 21, 8, 11, 58, 
    22, 8, 47, 51, 24, 8, 40, 0, 29, 8, 55, 12, 32, 8, 0, 29, 40, 8, 49, 50, 
    42, 8, 56, 21, 45, 8, 51, 24, 47, 8, 50, 42, 49, 8, 42, 49, 50, 8, 24, 47, 
    51, 8, 61, 15, 54, 8, 12, 32, 55, 8, 21, 45, 56, 8, 22, 11, 58, 8, 15, 54, 
    61]));

