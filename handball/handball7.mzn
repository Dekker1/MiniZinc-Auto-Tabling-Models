%   Elitserien handboll -- generic model, needs specific:
%   - sets of teams for N and S divisions
%   - which teams to form complementary divisions
%   - derby sets
%   - venue unavailabilities
%
%   Jeff Larson <jeffreyl@kth.se>
%   Mats Carlsson <matsc@sics.se>

% * 14-team league

% * Form 2 divisions which hold a single round-robin tournament

% 1. Each 7-team division must hold a SRRT to start the season.

% 2. This must be followed by two SRRTs between the entire league, the
%    second SRRT being a mirror of the first.

% 3. There must be a minimum number of breaks in the schedule
%    (home-home pair or away-away pair).

% 4. Each team has one bye during the season (to occur during the
%    divisional RRT).

% 5. At no point during the season can the number of home and away
%    games played by a team differ by more than 1.

% 6. Any pair of teams must have consecutive meetings occur at different
%    venues. (AVR)

include "globals.mzn";

%% version codes

bool: dopresolve = true;

%% HAP patterns

int: A = 1; % away
int: B = 2; % bye
int: H = 3; % home

int: divsize = 7;

set of int: north_team = 1..7;
set of int: south_team = 8..14;
set of int: team = 1..14;
set of int: first_tour = 1..7;
set of int: second_tour = 8..20;
set of int: third_tour = 21..33;
set of int: period = 1..20;
set of int: allperiod = 1..33;
set of int: breakable = {0,9,11,13,15,17,19};

array[period,team] of var A..H: hap;
array[period,team] of var team: contestant;
array[team] of var breakable: break;

var int: cost;
array[team] of var team: rowof;	% rowof[i]=j means TEAMi gets row j of template
array[team] of var team: teamof;% the inverse of rowof

%% venue unavailability

array[team,allperiod] of 0..1: nohome;

%% division assignment

set of int: group1;
set of int: group2;

%% derby constraints

array[int] of set of int: derby_set; % unused
array[int] of period: derby_period;  % unused

%% complementary schedules

array[int] of set of int: cpairs; % unused

%% cost table

array[int,int] of int: costtable; % unused

%% search heuristic

array[team] of team: heur;	% unused

%% DFA states

int: INIT = 1;
int: B_1 = 2;
int: A_1 = 3;
int: H_1 = 4;
int: A_2 = 5;
int: H_2 = 6;
int: AB_2 = 7;
int: HB_2 = 8;
int: A_3 = 9;
int: H_3 = 10;
int: AB_3 = 11;
int: HB_3 = 12;
int: A_4 = 13;
int: H_4 = 14;
int: AB_4 = 15;
int: HB_4 = 16;
int: A_5 = 17;
int: H_5 = 18;
int: AB_5 = 19;
int: HB_5 = 20;
int: A_6 = 21;
int: H_6 = 22;
int: AB_6 = 23;
int: HB_6 = 24;
int: AB_7 = 25;
int: HB_7 = 26;
int: AB_8 = 27;
int: HB_8 = 28;
int: AB_9 = 29;
int: HB_9 = 30;
int: AB_20 = 31;
int: HB_20 = 32;

array[int,int] of int: transition =
    		  [|  A_1,   B_1,   H_1  % INIT, start state
		   | AB_2,     0,  HB_2  % B_1
		   |    0,  AB_2,   H_2  % A_1
		   |  A_2,  HB_2,     0  % H_1
		   |    0,  AB_3,   H_3  % A_2
		   |  A_3,  HB_3,     0  % H_2
		   |    0,     0,  HB_3  % AB_2
		   | AB_3,     0,     0  % HB_2
		   |    0,  AB_4,   H_4  % A_3
		   |  A_4,  HB_4,     0  % H_3
		   |    0,     0,  HB_4  % AB_3
		   | AB_4,     0,     0  % HB_3
		   |    0,  AB_5,   H_5  % A_4
		   |  A_5,  HB_5,     0  % H_4
		   |    0,     0,  HB_5  % AB_4
		   | AB_5,     0,     0  % HB_4
		   |    0,  AB_6,   H_6  % A_5
		   |  A_6,  HB_6,     0  % H_5
		   |    0,     0,  HB_6  % AB_5
		   | AB_6,     0,     0  % HB_5
		   |    0,  AB_7,     0  % A_6
		   |    0,  HB_7,     0  % H_6
		   |    0,     0,  HB_7  % AB_6
		   | AB_7,     0,     0  % HB_6
		   |    0,     0,  HB_8  % AB_7
		   | AB_8,     0,     0  % HB_7
		   |    0,     0,  HB_9  % AB_8, accept state
		   | AB_9,     0,     0  % HB_8, accept state
		   |AB_20,     0,  HB_8  % AB_9
		   | AB_8,     0, HB_20  % HB_9
		   |    0,     0, HB_20  % AB_20, accept state
		   |AB_20,     0,     0  % HB_20, accept state
		   |];

% cost function

predicate part_cost(var breakable: bt, var team: r, var team: t, var 0..max(allperiod): part) ::presolve = (
    if dopresolve then
	bt in breakable /\
	let {array[period] of var A..H: lhap} in (
	    channel_break_hap(bt, lhap, r) /\
	    part = sum(p in period     where nohome[t,p]=1)(bool2int(lhap[p]                            =H)) +
	           sum(p in third_tour where nohome[t,p]=1)(bool2int(lhap[min(third_tour)+max(period)-p]=A))
	    )
    else
	    part = sum(p in period     where nohome[t,p]=1)(bool2int(hap[p,r]                            =H)) +
	           sum(p in third_tour where nohome[t,p]=1)(bool2int(hap[min(third_tour)+max(period)-p,r]=A))
    endif
);

constraint
    if not dopresolve then
	cost = sum(t in team, p in period  where nohome[t,p]=1)(bool2int(hap[p,rowof[t]]=H))
	     + sum(t in team, p in third_tour where nohome[t,p]=1)(bool2int(hap[min(third_tour)+max(period)-p,rowof[t]]=A))
    else
        let {array[team] of var 0..max(allperiod): rowcost} in (
	    forall(t in team)(part_cost(break[t], t, teamof[t], rowcost[t])) /\
	    cost = sum(t in team)(rowcost[t])
	)
    endif;

% division assignment

constraint
    let {var bool: NS} in (
	forall(t in group1)(NS <-> rowof[t] in north_team) /\
	forall(t in group2)(NS <-> rowof[t] in south_team)
    );

constraint
    inverse(rowof,teamof) :: domain;

%% STRUCTURAL CONSTAINTS

% first round robin tournament (domains)
constraint
    forall(p in first_tour, t in north_team)(
        contestant[p,t] in north_team
    ) /\
    forall(p in first_tour, t in south_team)(
        contestant[p,t] in south_team
    );

% channel break <---> hap (2)
predicate channel_break_hap(var breakable: bt, array[period] of var A..H: hapt, var team: t) ::presolve(model) =
	bt in breakable /\
	(t in north_team -> hapt[(t mod divsize)+1] = A) /\
	(t in south_team -> hapt[(t mod divsize)+1] = H) /\
	hapt[((t-1) mod divsize)+1] = B /\
	forall(p in breakable diff {0})(
	    bt = p <-> hapt[p]=hapt[p+1]
	) /\
	regular([hapt[p] | p in period],
		HB_20, % last state
		H,     % last symbol
		transition,
		INIT,  % start state
		{AB_8,HB_8,AB_20,HB_20} % accept states
		);

constraint
    forall(t in team)(
	channel_break_hap(break[t], [hap[p,t] | p in period], t)
    );

% RRT (5)
constraint
    forall(p in period)(
        inverse([contestant[p,t] | t in team],[contestant[p,t] | t in team]) :: domain
    );

% RRT (6)
constraint
    forall(t in team)(
        alldifferent([contestant[p,t] | p in first_tour]) :: domain /\
        alldifferent([contestant[p,t] | p in second_tour]) :: domain
    );

% either we at home and contestant away (7)
%     or we away and contestant at home
%     or bye (we = contestant)
constraint
    forall(p in period, t in team)(
        let {var team: ctw = contestant[p,t]} in (
	    hap[p,ctw] + hap[p,t] = A+H
	)
    );

% AVR rule (1) (8)
constraint
    forall(t in team)(
        alldifferent([3*contestant[p,t]+hap[p,t] | p in period]) :: domain
    );

%% IMPLIED CONSTRAINTS

% channel contestant <---> hap (3)
constraint
    forall(t in team, p in period)(
        contestant[p,t]=t <-> hap[p,t]=B
    );

% exactly two occurrences of every break period (12)
constraint
    global_cardinality_closed(break, [i | i in breakable], [2 | i in breakable]) :: domain;

%% SYMMETRY-BREAKING CONSTAINTS

% 1st row and 1st column complementary for each division (18)
constraint
    forall(t in north_team)(
	hap[t,1] + hap[1,t] = A+H /\
	hap[t,1+divsize] + hap[1,t+divsize] = A+H
    );

%% SOLVING AND OUTPUTTING

solve :: seq_search(
    [int_search([hap[p,t] | p in period, t in team], input_order, indomain_min, complete),
     int_search(rowof, input_order, indomain_min, complete),
     int_search([contestant[p,t] | t in team, p in period], input_order, indomain_min, complete)
     ]
    ) minimize(cost);

output [show(cost)];
