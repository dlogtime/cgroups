##################################################################################################################################
##################################################################################################################################
##
## Code, accompanying the paper "Generation of finite groups with cyclic Sylow subgroups" (C- or Z-groups)  
## 
##     by Heiko Dietrich and Darren Low (C) 2020
##
## Heiko Dietrich, School of Mathematics, Monash University, Australia
## http://users.monash.edu/~heikod/
## heiko.dietrich@monash.edu
##
## Darren Low, School of Mathematics, Monash University, Australia
## dslow3@student.monash.edu 
##
##################################################
##
## This code requires GAP 4.10.0 or newer. It provides the functionality to construct and identify
## C-groups (finite groups that have cyclic Sylow subgroups). 
##
## User functions:
##
##   IsCGroup(G)       : tests whether a finite group is a C-group
##   NumberOfCGroups(n): outputs the number if isomorphism types of C-groups of order n
##   CGroupById(n,i)   : returns the C-group with id [n,i], the i-th group in our database
##   IdCGroup(G)       : returns the id [n,i] of a C-group G, such that G is isomorphic to CGroupById(n,i)
##   AllCGroups(n)     : returns all C-groups of order n, up to isomorphism
##
## For each order n, there exist N=NumberOfCGroups(n) many isomorphism types of C-groups of order n. In our implementation
## these N groups can be constructed by AllCGroups(n) or by CGroupById(n,i) where i in [1..N]. The ID of a C-group G of
## order n is the unique i in [1..N] such that G is isomorphic to CGroupById(n,i).
##
##################################################
##
##
## At the moment, groups are constructed as pc-groups using GroupByRwsNC; set the following to "false" if the code should 
## not use the NC-version of GroupByRws
##

USE_NC:=true;

##
##
##################################################################################################################################
##################################################################################################################################
##
##
## Internal functions are saved in the name space record cgrp_record 
##

cgrp_record := rec();
DeclareAttribute( "cgroup_id", IsGroup );

##
##
##################################################################################################################################
##################################################################################################################################



########################################################################################
#
# tests if a group G is a C-group (all Sylow subgroups cyclic)
# (alternative test would be to test if G' and G/G' are coprime and cyclic
#
########################################################################################
IsCGroup := function(G)
local facs, syl, hom, Gs;
   if Size(G)=1 then return true; fi;

   Gs := DerivedSubgroup(G);
   if not IsCyclic(Gs) then return false; fi;
   hom := Image(NaturalHomomorphismByNormalSubgroup(G,Gs));
   if not Gcd(Size(Gs),Size(hom))=1 or not IsCyclic(hom) then return false; fi;
   return true;

   facs := List(Collected(FactorsInt(Order(G))),x->x[1]);
   syl  := List(facs,x->SylowSubgroup(G,x));
   return ForAll(syl,IsCyclic);
 end;




########################################################################################
# takes in a list of numbers L
# returns the tuples of things
# where each tuple W has W[i] <= L[i] 
# NZ version doesn't have 0
########################################################################################
cgrp_record.zTuples := function(L)
local W, V, k;

	V := [];
	W := [];
    for k in L do Add(W, 0); od;
    while not W = L do 
    	k := 1;
        Add(V, StructuralCopy(W));
        while k <= Length(L) do
        	W[k] := W[k] + 1;
            if W[k] > L[k] then
            	W[k] := 0;
                k := k + 1;
            else
                k := Length(L) + 1;
            fi;
        od;
    od;
    Add(V, W);
    
    return V;    
end;


########################################################################################
# takes in a list of numbers L
# returns the tuples of things
# where each tuple W has W[i] <= L[i] 
# NZ version doesn't have 0
########################################################################################
cgrp_record.zTuplesNZ := function(L)
local W, V, k;

	V := [];
	W := [];
    for k in L do Add(W, 1); od;
    while not W = L do
    	k := 1;
        Add(V, StructuralCopy(W));
        while k <= Length(L) do
        	W[k] := W[k] + 1;
            if W[k] > L[k] then
            	W[k] := 1;
                k := k + 1;
            else
                k := Length(L) + 1;
            fi;
        od;
    od;
    Add(V, W);
    
    return V;
end;

###################################################################################
# get possible acting group orders
###################################################################################
cgrp_record.getOrders := function(n, d)
local e, P, Q, expo, p, q, guac, max, M;

    e := n/d;
    P := Collected(FactorsInt(d));
    Q := Collected(FactorsInt(e));
    expo := [];
    for p in P do
        max := 1;
        for q in Q do
            guac := Gcd(q[1]-1, p[1]^p[2]);
            if guac = 1 then continue; fi;
            guac := LogInt(guac, p[1]);
            if guac > max then max := guac; fi;
        od;
        Add(expo, max);
    od;
    M := List(cgrp_record.zTuplesNZ(expo), m-> Product([1..Length(m)], x-> P[x][1]^m[x]));
    Sort(M);

return M;
end;


###################################################################################
# cluster function
###################################################################################
cgrp_record.getClusters := function(n, d, m)
local P, Q, Qfacs, expo, act, ip, Pacts, maxPacts, q, qfac, res, epos, ie, front, back, f, b, tmp, sizes, comb,p,e;

    #####
	# Now we determine the clusters corresponding to the acting group order m
	# We note which primes can be acted on, and the maximal exponent which can occur
	#####
    P := Collected(FactorsInt(d));
    Q := Collected(FactorsInt(n/d));
    Qfacs := List(Q, q-> rec(prime:=q, facs:=Collected(FactorsInt(q[1]-1))));
    expo := List(Collected(FactorsInt(m)), x-> x[2]);
    act := [];
    for ip in [1..Length(P)] do
        p := P[ip][1];
        e := expo[ip];
        Pacts := [];
        maxPacts := [];
        for q in Qfacs do for qfac in q.facs do
            if qfac[1] = p then
                Add(Pacts, q.prime);
                Add(maxPacts, Minimum(e, qfac[2]));
                continue;
            fi;
        od; od;
        res := [];
        
        ######
		# epos has the possible positions which p can act maximally with exponent e
		# we sort this by fixing the first position that has entry e
		# then populating entries before that lexicographically with values between 0
		# and min(entry,e-1)
		# and then those after lexicographically with values between 
		# 0 and min(entry,e) using zTuples
		#####
        epos := Filtered([1..Length(Pacts)], x-> maxPacts[x]=e);
        for ie in epos do
            front := cgrp_record.zTuples(List(maxPacts{[1..ie-1]}, x-> Minimum(x,e-1)));
            back  := cgrp_record.zTuples(List(maxPacts{[ie+1..Length(maxPacts)]}, x-> Minimum(x,e)));
            for f in front do for b in back do
                tmp := Concatenation([f,[e],b]);
                tmp := Filtered(List([1..Length(Pacts)], x-> [p,Pacts[x][1],tmp[x]]), y-> not y[3]=0);
            Add(res, tmp);
            od; od;
        od;
        Add(act, res);
    od;
    
    #########
	# for each acting prime, we get the collection of 
	# all sets of primes and exponents it can act on
	# a cluster is formed by choosing one such set for each acting prime
	# we take all possible combinations
	#########
    sizes := List(act,Size);
    comb := cgrp_record.zTuplesNZ(sizes);
    
    return List(comb, x-> Concatenation(List([1..Length(P)],i-> act[i][x[i]])));
end;



######################################################################################
# Murty nu function
######################################################################################
cgrp_record.nu := function(p, e)
	return LogInt(Product(Collected(FactorsInt(e)), q-> Gcd(p[1]^p[2], q[1]-1)), p[1]);
end;


########################################################################################
# Murty Cd function; counts number of order n with acting divisor d
########################################################################################
cgrp_record.Cd := function(n, d)
local p, e, product, j, sum;

	if d = 1 then return 1; fi;
	e := n/d;
	if d = n or not Gcd(d,e)=1 then return 0; fi;
	
	product := 1;
	for p in Collected(FactorsInt(d)) do
		sum := 0;
		j := 1;
		while j <= p[2] do
			sum := sum + (p[1]^cgrp_record.nu([p[1],j],e)-p[1]^cgrp_record.nu([p[1],j-1],e))/Phi(p[1]^j);
			j := j + 1;
		od;
		product := product * sum;
	od;	
	
	return product;
end;



###################################################################################
# Murty Cdm; function counts number of order n with acting divisor d and acting group order m
###################################################################################
cgrp_record.Cdm := function(n, d, m)
local p, e, product, tmp;

	if d = 1 then return 1; fi;
	e := n/d;
	if d = n or not Gcd(d,e)=1 or m=1 then return 0; fi;
	
	product := 1;
	for p in Collected(FactorsInt(m)) do
		tmp := (p[1]^cgrp_record.nu([p[1],p[2]],e)-p[1]^cgrp_record.nu([p[1],p[2]-1],e))/Phi(p[1]^p[2]);
		product := product * tmp;
	od;	
	
	return product;
end;



#########################################################################################
# ClusterCount counts number of groups in cluster c
#########################################################################################
cgrp_record.ClusterCount := function(c)
local current, total, max, t;

	current := 0;
	total := 1;
	for t in c do
		if not t[1] = current then
			current := t[1];
			max := t[3];
		elif t[3] > max then
			total := total * Phi(t[1]^max);
			max := t[3];
		else
			total := total * Phi(t[1]^t[3]);
		fi;
	od;
	
	return total;
end;



###########################################################################################
#
# The number of C-groups of order n, up to isomorphism 
#
###########################################################################################
NumberOfCGroups := function(n)
local d, N, D, sum;
	
	######
	# take only primes that can possibly act
	# and then product their max powers together
	######
	N := Collected(FactorsInt(n));
	D := List(Combinations(Filtered(N{[1..Length(N-1)]}, p-> ForAny(N{[2..Length(N)]}, q-> not Gcd(q[1]-1,p[1])=1))), w-> Product(List(w, x-> x[1]^x[2])));
	sum := 0;
	for d in D do
        sum := sum + cgrp_record.Cd(n, d);
	od;

	return sum;
end;	



#############################################################################################
# Fast exponentiation, b = base, e = exponent, m = modulus
#############################################################################################
cgrp_record.FastExponentiation := function(b,e,m)
local s;
    
    s := 1;
    while e > 0 do 
        if (e mod 2) = 1 then s := (s*b) mod m; fi;
        e := QuoInt(e,2);
        b := (b*b) mod m;
    od;
    
    return s;
end;



###########################################################################################
#
# Constructs the C-group with id [n,id]
#
###########################################################################################
CGroupById := function(n, id)
local N, D, sum, i, j, k, d, M, e, guac, max, p, ip, q, P, Q,  myid,expo, m, res, tmp, act,
clusters, coll, orders, F, gens, C, c, orb, iq, Qprime, current, ttt, tstart, padic, G;


        if not (IsInt(n) and n>0) or not (IsInt(id) and id>0) then
	   Error("wrong input");
	elif id > NumberOfCGroups(n) then
	   Error("There are only ",NumberOfCGroups(n), " many C-groups of order ",n);
	fi;

        myid := [n,id];

	tstart := Runtime();
	#####
	# Deal with the cases in which there is only 1 group
	#####
	if n = 1 then 
           G:=GroupByRws(SingleCollector(FreeGroup(0:FreeGroupFamilyType:="syllable"), 1));
	   Setcgroup_id(G,myid);
	   return G;
       fi; 
	N := Collected(FactorsInt(n));
	if Length(N)=1 or Gcd(n,Phi(n))=1 or id=1 then
        orders := [];
        for p in N do
            i := 1;
            while i <= p[2] do
                Add(orders, p[1]);
                i := i + 1;
            od;
        od;
        F := FreeGroup(Length(orders):FreeGroupFamilyType:="syllable");
        gens := GeneratorsOfGroup(F);
        coll := SingleCollector(F, orders);
        i := 1;
        j := 1;
        while j <= Length(N) do
            k := 1;
            while k < N[j][2] do
                SetPowerNC(coll, i+k-1, gens[i+k]);
                k := k + 1;
            od;
            i := i + k;
            j := j + 1;
        od;
        if not id=1 then
            Print("Hold up, there's only 1 Z-group of order ",n,"!\n");
        fi;
        if USE_NC then
	    G:=GroupByRwsNC(coll);
	else
	   G:=GroupByRws(coll);
        fi;
	Setcgroup_id(G,myid);
	return G;
    fi;
	
	#####
	# First we determine the acting divisor
	# Start from sum=1 and d\neq 1 because we know it's not cyclic
	#####
	D := List(Combinations(Filtered(N{[1..Length(N-1)]}, p-> ForAny(N{[2..Length(N)]}, q-> not Gcd(q[1]-1,p[1])=1))), w-> Product(List(w, x-> x[1]^x[2])));
	Sort(D);
	sum := 1;
	i := 1;
	while sum < id do 
		i := i + 1;
		if i > Length(D) then Error("id too large\n"); fi;
		if not Gcd(D[i],n/D[i])=1 then continue; fi;
		tmp := cgrp_record.Cd(n, D[i]);
		sum := sum + tmp;
	od;
	d := D[i];
	id := tmp - sum + id;
	#Print("took ",Runtime() - ttt," to find acting divisor\n");
	#ttt := Runtime();
	
	####
	# Next we determine the acting group order
	####
	M := cgrp_record.getOrders(n, d);
	sum := 0;
	i := 0;
	while sum < id do 
		i := i + 1;
		tmp := cgrp_record.Cdm(n, d, M[i]);
		sum := sum + tmp;
	od;
	m := M[i];
	id := tmp - sum + id;
	#Print("took ",Runtime() - ttt," to find acting group order\n");
	#ttt := Runtime();
	clusters := cgrp_record.getClusters(n,d,m);
	
	#####
	# finding which cluster and the position within it
	# we subtract 1 from the position to help with conversion to mixed base later
	#####
	sum := 0;
	i := 0;
	while sum < id do 
		i := i + 1;
		tmp := cgrp_record.ClusterCount(clusters[i]);
		sum := sum + tmp;
	od;
	C := clusters[i];
	id := tmp - sum + id - 1;
	#Print("took ",Runtime() - ttt," to find cluster\n");
	#ttt := Runtime();
	
	#######
	# finally we build yay
	# here we get the prime orders and also
	# record for each prime factor: the position of the generator in the collector of that order
	# we arrange the primes such that acting primes come first, then acted on primes, then the central ones. 
	#######
	tmp := [];
	res := [];
	Q := Collected(FactorsInt(n/d));
	for q in Q do
        if ForAny(C, c-> c[2]=q[1]) then
            Add(tmp, q);
        else
            Add(res, q);
        fi;
    od;
    Q := Concatenation(tmp, res);
    orders:= FactorsInt(d);
    P := Collected(orders);
	k := 1;
    for p in P do
        Add(p, k);
        k := k + p[2];
    od;
    for q in Q do
        i := 1;
        while i <= q[2] do
            Add(orders, q[1]);
            i := i + 1;
        od;
        Add(q, k);
        k := k + q[2];
    od;
    
    #####
    # setting relative orders
    #####
	F := FreeGroup(Length(orders):FreeGroupFamilyType:="syllable");
	gens := GeneratorsOfGroup(F);
	coll := SingleCollector(F, orders);
    i := 1;
	j := 1;
	while i <= Length(P) do
		k := 1;
		while k < P[i][2] do
			SetPowerNC(coll, j+k-1, gens[j+k]);
			k := k + 1;
		od;
		i := i + 1;
		j := j + k;
	od;
	i := 1;
	while i <= Length(Q) do
		k := 1;
		while k < Q[i][2] do
			SetPowerNC(coll, j+k-1, gens[j+k]);
			k := k + 1;
		od;
		i := i + 1;
		j := j + k;
	od;
	
    #####
    # adding the conjugation exponents
    # orb is the number of possible orbits
    # ip(iq) is the position of current acting(acted on) prime in P(Q)
    # k corresponds to the k-th possible action of p on q with exponent exp
    #####
    Qprime := List(Q, x-> x[1]);
    current := 0;
    ip := 0;
    #Print(orders, " are our orders\n");
    #Print(C, " is our cluster\n");
    #Print(P, " is our P\n");
    #Print(Q, " is our Q\n");
    for c in C do
        if not c[1] = current then
            current := c[1];
            orb := 1;
            max := c[3];
            ip := ip + 1;
            iq := 0;
        elif c[3] > max then
            orb := Phi(c[1]^max);
            max := c[3];
        else
            orb := Phi(c[1]^c[3]);
        fi;
        p := c[1]^c[3];
        iq := Position(Qprime, c[2], iq);
        q := c[2]^Q[iq][2];
        k := RemInt(id, orb) + 1;
        id := QuoInt(id, orb);
        
        #####
        # This loop here is to skip over actions which are of the wrong exponent
        #####
        for tmp in [1..QuoInt(k, c[1])] do
            k := k + 1;
            if not Gcd(k, c[1]) = 1 then k := k + 1; fi;
        od;
        
        for i in [1..c[3]] do for j in [1..Q[iq][2]] do
            #Print(i," is our i, ",j," is our j\n");
            tmp := cgrp_record.FastExponentiation(PrimitiveRootMod(q),k*Phi(q)/(c[1]^(1+c[3]-i)), c[2]^(Q[iq][2]+1-j));
            padic := [RemInt(tmp, c[2])];
            tmp := QuoInt(tmp, c[2]);
            while not tmp = 0 do
                Add(padic, RemInt(tmp, c[2]));
                tmp := QuoInt(tmp, c[2]);
            od;
            res := Product([1..Length(padic)], x-> gens[Q[iq][3]+j+x-2]^padic[x]);            
            SetConjugateNC(coll, Q[iq][3]+j-1, P[ip][3]+i-1, res);
        od; od;
    od;
   if USE_NC then
      G:=GroupByRwsNC(coll);
   else
      G:=GroupByRws(coll);
   fi;
   Setcgroup_id(G,myid);
   return G;
end;




####################################################################################################
# Identification function
# For a C-Group G, return its Id
#
#
# "cluster" will contain triplets of prime actions
# "orb" is the number of non isomorphic actions
# "pos" has position of which action takes place 
# "Pot" has positions of primes which could potentially act, i.e. there is a q-1 not coprime;
# "D" has the positions of primes which do act
####################################################################################################
IdCGroup := function(G)
local id, n, N, ip, iq, p, q, e, pup, qup, x, y, k, cluster, orb, first, max, r, s, norm, gens, pos, i, P, Q, d, m, D, M, expo, current, cpos, act , res, tmp, clusters, Pot, c, flag2, flag, ig, ttt, oldmax, next;


    if Hascgroup_id(G) then return cgroup_id(G); fi;
    if Size(G)=1 then
       res := [1,1];
       Setcgroup_id(G,res);
       return res;
    fi;
    
    ttt := Runtime();
    n := Size(G);
    N := Collected(FactorsInt(n));
    gens := [];
    for i in N do 
        tmp := MinimalGeneratingSet(SylowSubgroup(G, i[1]));
        if not Size(tmp) = 1 then Error("Input is not a C-group!\n"); fi;
        Add(gens, tmp[1]);
    od;
    #Print(Runtime()-ttt, " to get gens\n"); 
    cluster := [];
    orb := [];
    pos := [];
    D := [];
    Pot := [];
    for ip in [1..Length(N)-1] do 
        first := 1;
        x := gens[ip];
        for iq in [ip..Length(N)] do
            if Gcd(N[ip][1], N[iq][1]-1) = 1 then continue; fi;
            if first = 1 then Add(Pot, ip); first := 2; fi;
            y := gens[iq];
            ####
            # if p acts on q
            ####
            if not y^x = y then
                #Print("we found a non-trivial action\n");ttt:=Runtime();
                p := N[ip][1];
                q := N[iq][1];
                e := 1;
                ####
                # we determine the exponent
                ####
                while not y^(x^(p^e)) = y do e := e+1; od;
                #Print(Runtime()-ttt, " to get the exp of the action\n");
                Add(cluster, [p,q,e]);
                pup := p^e;
                qup := q^N[iq][2];
                r := PrimitiveRootMod(qup);
                s := Phi(qup)/pup;
                
                ####
                # "normalise" the acting generator if first time
                # otherwise, count number of orbits and check which action occurs,
                # adding the counter for that action to "pos"
                ####
                if first = 2 then
                    ttt:=Runtime();
                    first := 0;
                    Add(D, ip);
                    max := e;
                    Add(orb, 1);
                    Add(pos, 1);
                    norm := 1;
                    while not y^(x^norm) = y^(cgrp_record.FastExponentiation(r, s, qup)) do
                        norm := norm + 1;
                        #Print(norm, " norm up!\n");
                    od;
                    x := x^norm;
                    gens[ip] := x;
                    #Print("this is the first: e is ",e," out of ",N[ip][2],"\n");
                    #Print(Runtime()-ttt, " to normalise gen\n");
                    #Print(gens[ip], " all my gens\n");
                else
                    #Print("next action!\n");
                    flag2 := 0;
                    if e > max then
                        Add(orb, Phi(p^max));
                        oldmax := max;
                        max := e;
                    else
                        Add(orb, Phi(p^e));
                    fi;
                    tmp := [];
                    ttt := Runtime();
                    i := 1;
                    k := 1;
                    next := 1;
                    while not y^x = y^(cgrp_record.FastExponentiation(r, k*s, qup)) do
                        i := i+1;
                        k := k+1;
                        if not Gcd(p, k) = 1 then 
                            k := k+1;
                        fi;
                        if i > orb[Length(orb)] then
                            #Print(x, " going up\n");
                            i := 1;
                            k := 1;
                            x := gens[ip]^((next*p^oldmax)+1);
                            next := next+1;
                        fi;
                    od;
		    gens[ip] := x; ##new!
                    Add(pos,i);
                    #Print(Runtime() - ttt, " to find the right canonical action\n");
                fi;
            fi;
        od;
    od;
    if D = [] then
       res := [n,1];
       Setcgroup_id(G,res);
       return res;
    fi;
    #Print("position vector is ",pos," out of ");
    #Print(orb,"\n");
    
    ######
    # here we convert the position vector into the actual
    # numerical position within the cluster.
    ######
    ttt := Runtime();
    cpos := 0;
    for i in [1..Length(pos)] do
        k := 1 + Length(pos) - i;
        if not k = 1 then 
            cpos := (cpos + pos[k]-1)*orb[k-1];
        fi;
    od;
    cpos := cpos + pos[1];
    #Print(Runtime()-ttt," to get cluster pos\n");ttt:=Runtime();
    #Print(cpos," is my cluster position\n");
    
    #############
    # we find the acting divisor using Murty's Cd formula
    #############
    d := Product(D, x-> N[x][1]^N[x][2]);
    Pot := List(Combinations(Pot), x-> Product(N{x}, y-> y[1]^y[2]));
    Sort(Pot);
    i := 1;
    id := 0;
    while i < Position(Pot, d) do
        id := id + cgrp_record.Cd(n, Pot[i]);
        i := i + 1;
    od;
    #Print(Runtime()-ttt," to get acting div\n");ttt:=Runtime();
    #Print(d, " is my acting divisor\n");
    #Print(Pot , " are all possible acting divisors\n");
    #Print(id, " is how many in previous divisors\n");
    
    #########
    # now for acting group order using Murty's Cdm formula
    #########
    current := 0;
    max := 0;
    m := 1;
    for c in cluster do
        if not c[1] = current then 
            if not current = 0 then
                m := m*(current^max);
            fi;
            current := c[1];
            max := c[3];
        elif c[3] > max then
            max := c[3];
        fi;
    od;
    m := m*(current^max);
	M := cgrp_record.getOrders(n, d);
    
    i := 1;
	while i < Position(M, m) do
        id := id + cgrp_record.Cdm(n, d, M[i]);
        i := i + 1;
    od;
    #Print(m, " is my acting order\n");
    #Print(M, " are all possible acting orders\n");
    #Print(id , " is how many in previous acting groups \n");
    #Print(Runtime()-ttt," to get acting order\n");ttt:=Runtime();
    ##########
    # finally construct clusters and find position of the cluster 
    ##########
	clusters := cgrp_record.getClusters(n, d, m);
	
	i := 1;
	while i < Position(clusters,cluster) do
        id := id + cgrp_record.ClusterCount(clusters[i]);
        i := i + 1;
    od;
    #Print(Runtime()-ttt," to get cluster\n"); ttt:=Runtime();
    #Print(cluster, " is my cluster in position ", Position(clusters,cluster), "\n");
    #Print(clusters, " is all clusties\n"); 
    #Print(id, " is how many in previous clusties\n");

       res := [n,id+cpos];
       Setcgroup_id(G,res);
       return res;
end;




#################################################################################################
# input: integer n, integer d such that d|n and gcd(n/d, d) = 1, and a cluster (triplets)
# Builds all the groups of order n with acting divisor in the cluster
#################################################################################################
cgrp_record.zBuildCluster := function(n, d, C)
local N, e, Q, q, tmp, P, k, res, p, orders, boll, id, F, gens, ip, iq, max , orb, L, i, j, coll, c, Qprime, current, padic, G;
    

    N := FactorsInt(n);
    if d = 1 then
        N := Collected(N);
        orders := [];
            for p in N do
                i := 1;
                while i <= p[2] do
                    Add(orders, p[1]);
                    i := i + 1;
                od;
            od;
            F := FreeGroup(Length(orders):FreeGroupFamilyType:="syllable");
            gens := GeneratorsOfGroup(F);
            coll := SingleCollector(F, orders);
            i := 1;
            j := 1;
            while j <= Length(N) do
                k := 1;
                while k < N[j][2] do
                    SetPowerNC(coll, i+k-1, gens[i+k]);
                    k := k + 1;
                od;
                i := i + k;
                j := j + 1;
            od;
	G := GroupByRws(coll);
	Setcgroup_id(G,[n,1]);
        return [G];
    fi;
    e := n/d;
    tmp := [];
	res := [];
	for q in Collected(FactorsInt(e)) do
        if ForAny(C, c-> c[2]=q[1]) then
            Add(tmp, q);
        else
            Add(res, q);
        fi;
    od;
    Q := Concatenation(tmp, res);
    P := Collected(FactorsInt(d));
    #####
    # recording the position of each prime
    #####
	orders := [];
	k := 1;
	for p in P do
        i := 1;
        while i <= p[2] do
            Add(orders, p[1]);
            i := i + 1;
        od;
        Add(p, k);
        k := k + p[2];
    od;
    for q in Q do
        i := 1;
        while i <= q[2] do
            Add(orders, q[1]);
            i := i + 1;
        od;
        Add(q, k);
        k := k + q[2];
    od;
	
	#####
	# setting relative orders
	#####
	F := FreeGroup(Length(orders):FreeGroupFamilyType:="syllable");
	gens := GeneratorsOfGroup(F);
	i := 1;
    j := 1;
    boll := SingleCollector(F, orders);
    while i <= Length(P) do
        k := 1;
        while k < P[i][2] do
            SetPowerNC(boll, j+k-1, gens[j+k]);
            k := k + 1;
        od;
        i := i + 1;
        j := j + k;
    od;
    i := 1;
    while i <= Length(Q) do
        k := 1;
        while k < Q[i][2] do
            SetPowerNC(boll, j+k-1, gens[j+k]);
            k := k + 1;
        od;
        i := i + 1;
        j := j + k;
    od;
    L := [];
    Qprime := List(Q, x-> x[1]);
	for id in [0..cgrp_record.ClusterCount(C)-1] do 
        #Print("Building the position ",id+1," group in this clust\n");
        coll := StructuralCopy(boll);
        ip := 0;
        current := 0;
        for c in C do
            if not c[1] = current then
                current := c[1];
                orb := 1;
                max := c[3];
                ip := ip + 1;
                iq := 0;
            elif c[3] > max then
                orb := Phi(c[1]^max);
                max := c[3];
            else
                orb := Phi(c[1]^c[3]);
            fi;
            p := c[1]^c[3];
            iq := Position(Qprime, c[2], iq);
            q := c[2]^Q[iq][2];
            k := RemInt(id, orb) + 1;
            id := QuoInt(id, orb);
            
            #####
            # This loop here is to skip over actions which are of the wrong exponent
            #####
            for tmp in [1..QuoInt(k, c[1])] do
                k := k + 1;
                if not Gcd(k, c[1]) = 1 then k := k + 1; fi;
            od;
            
            for i in [1..c[3]] do for j in [1..Q[iq][2]] do
                #Print(i," is our i, ",j," is our j\n");
                tmp := cgrp_record.FastExponentiation(PrimitiveRootMod(q),k*Phi(q)/(c[1]^(1+c[3]-i)), c[2]^(Q[iq][2]+1-j));
                padic := [RemInt(tmp, c[2])];
                tmp := QuoInt(tmp, c[2]);
                while not tmp = 0 do
                    Add(padic, RemInt(tmp, c[2]));
                    tmp := QuoInt(tmp, c[2]);
                od;
                res := Product([1..Length(padic)], x-> gens[Q[iq][3]+j+x-2]^padic[x]);            
                SetConjugateNC(coll, Q[iq][3]+j-1, P[ip][3]+i-1, res);
            od; od;
        od; 
        if USE_NC then Add(L, GroupByRwsNC(coll)); else Add(L, GroupByRws(coll)); fi;
    od;
	
	return L;
end;



#######################################################################################
#
# Return all C-groups of order n up to isomorphism
#
#######################################################################################
AllCGroups := function(n)
local L, D, N, d, m, M, C, clusters,i;
    
    if n = 1 then return [GroupByRws(SingleCollector(FreeGroup(0:FreeGroupFamilyType:="syllable"), 1))]; fi;
    N := Collected(FactorsInt(n));
    L := cgrp_record.zBuildCluster(n,1, []);
	D := List(Combinations(Filtered(N{[1..Length(N-1)]}, p-> ForAny(N{[2..Length(N)]}, q-> not Gcd(q[1]-1,p[1])=1))), w-> Product(List(w, x-> x[1]^x[2])));
	Sort(D);
	Remove(D, 1);
	#Print(D," is all divisors\n");
    for d in D do
        if cgrp_record.Cd(n,d) = 0 then continue; fi;
        M := cgrp_record.getOrders(n, d);  
        #Print(M, " is all orders\n");
        for m in M do
            clusters := cgrp_record.getClusters(n, d, m);
            for C in clusters do
                Append(L, cgrp_record.zBuildCluster(n, d, C)); 
                #Print("appened\n");
            od;
        od;
    od;
    for i in [1..Size(L)] do Setcgroup_id(L[i],[n,i]); od;
    return L;
end;




