{*
August 29, 2016

Goal: check Lemma 5.2: if the rank is exactly one, 
then after removing the last column, the rank is still exactly one

*}


-- Given a tableau T, find the low row
-- Return a list of indices
lowRow = (T) -> (
    --Cj stands for column j in T
    Cj:={};
    i:=0;
    lr:=for j from 0 to #(T_0)-1 list (
	Cj=delete(null,apply(#T, i -> if #(T_i)>=j+1 then T_i_j));
	i=position(Cj, x -> x==0,Reverse=>true);
	if instance(i,ZZ) then {i,j}
    );
    delete(null,lr)
);


-- Given a partially filled tableau T
-- and some content with amount cj of flavor x
-- reverse fill T with that content
reverseFillContentj = (T,cj,x) -> (
    -- Make a list of the boxes to be filled
    lr:=lowRow(T);
    fillboxes:=reverse sort lowRow(T);
    fillboxes = drop(fillboxes,{cj,#fillboxes-1});
    -- Fill those boxes and copy the rest
    if #fillboxes < cj then error concatenate("The low row for flavor ",toString(x)," is only size ",toString(#fillboxes)) << endl;
    apply(#T, i -> apply(#(T_i), j -> if member({i,j},fillboxes) then x else T_i_j))
);


-- print a tableau nicely as a mutable matrix
-- This is only place we use matrices
printTableau = (T) -> (       
    M:=mutableMatrix(ZZ,#T,#(T_0));
    for i from 0 to #T-1 do (
	for j from 0 to #(T_i)-1 do (
            M_(i,j) = T_i_j	    
    ));
    return M
);


-- Reverse fill but only return the final answer
reverseFill= (w,l) -> (
    -- compute p and k
    s:=lift(sum(w)/2,ZZ);
    p:=s % l;
    k:=lift( (s-p)/l,ZZ);
    if p==0 then (
        p=l;
	k=k-1
    );
    Lambda:=sum drop(w, {0,2*k});
    -- create the shape of T with all entries 0
    T:=apply(2*k, i -> apply(l, j -> 0));
    T=append(T, apply(p, j -> 0));
    T=append(T, apply(p, j -> 0));
    for j from 0 to #w-1 do (
        T=reverseFillContentj(T, w_(#w-1-j),#w-j);
	--print concatenate("Fill with flavor ",toString(#w-j)) << endl;
	--print printTableau(T) << endl;
	--print "" << endl;
    );
    return T    
);

Tminusc = (w,l) -> (
    T:=reverseFill(w,l);    
    apply(#T, i -> delete(null, apply(#(T_i), j -> if j<l-1 then T_i_j)))  
);


-- check whether a list is weakly increasing
isWeaklyIncreasing = (L) -> (
    for i from 0 to #L-2 do (
        if L_(i+1) < L_(i) then return false	
    );    
    return true
);

-- check whether a list is strictly increasing
isStrictlyIncreasing = (L) -> (
    for i from 0 to #L-2 do (
        if L_(i+1) <= L_(i) then return false	
    );    
    return true
);

-- Check that T is a partition
-- That is, check that the sizes of the rows are weakly decreasing
isPartition = (T) -> (
    shape:=apply(#T, i -> #(T_i));
    isWeaklyIncreasing(reverse shape)
);

-- Check that T is semistandard
-- That is, want weakly increasing rows and strictly increasing columns
isSemistandard = (T) -> (
    -- Check that rows are weakly increasing
    for i from 0 to #T-1 do (
        if isWeaklyIncreasing(T_i)==false then return false;	
    );
    -- Check that columns are strictly increasing
    Cj:={};
    for j from 0 to #(T_0)-1 do (
	Cj=delete(null,apply(#T, i -> if #(T_i)>=j+1 then T_i_j));
        if isStrictlyIncreasing(Cj)==false then return false;	
    );
    return true
);

-- compute the content of T
tableauContent = (T) -> ( 
    A:=tally flatten T;
    n:=max flatten T;
    apply(n, i -> A#(i+1))
);

-- check whether T is proper
-- Def. T is proper if for all positive integers q such that r+1+q is a row 
-- in the first column of T, the flavor in row r+1+q column 1 is greater than
-- or equal to the flavor in row q column l (or this box is not in the tableau) 

-- Want: q>=1 and r+1+q <= #T
-- For sl_2, r=1 and l is the conformal block level
isProper = (T,r,l) -> (
    for q from 1 to #T-r-1 do (
        if #(T_(q-1)) < l-1 then continue;
	if T_(r+1+q-1)_0 < T_(q-1)_(l-1) then return false
    );
    return true
);


end





restart
load "CheckLemma5.2.m2"

-------------------------------
-------------------------------
--Examples
-------------------------------
-------------------------------

--Example 5.3:
printTableau reverseFill({9,8,8,8,8,8,8,2,1},9)
printTableau Tminusc({9,8,8,8,8,8,8,2,1},9)


---------------------------------
---------------------------------
-- Check all small levels for n=5
---------------------------------
---------------------------------
loadPackage("ConformalBlocks");
sl2=simpleLieAlgebra("A",1);

--n=5
Lemma52Examples = {};
time for l from 1 to 10 do (
 for i1 from 1 to l do (
  for i2 from 1 to i1 do (
   for i3 from 1 to i2 do (
    for i4 from 1 to i3 do (
     for i5 from 1 to i4 do (
      w=reverse sort {i1,i2,i3,i4,i5};    
      if odd(sum(w)) then continue;
      V=conformalBlockVectorBundle(sl2,l,apply(w, i -> {i}),0);
      r=conformalBlockRank(V);   
      if r!=1 then continue;
      Lemma52Examples = append(Lemma52Examples,{w,l});
      Tmc=Tminusc(w,l);
      if Tmc == apply(#Tmc, i -> {}) then continue;
      wprime=tableauContent(Tmc);
      Vprime=conformalBlockVectorBundle(sl2,l-1,apply(wprime, i -> {i}),0);
      rprime=conformalBlockRank(Vprime); 
      if rprime!=1 then error concatenate(toString({w,l}), " does not satisfy Lemma 5.2") << endl;
))))))
#Lemma52Examples

--n=6
time for l from 1 to 10 do (
 for i1 from 1 to l do (
  for i2 from 1 to i1 do (
   for i3 from 1 to i2 do (
    for i4 from 1 to i3 do (
     for i5 from 1 to i4 do (
      for i6 from 1 to i5 do (
      w=reverse sort {i1,i2,i3,i4,i5,i6}; 
      if odd(sum(w)) then continue;
      V=conformalBlockVectorBundle(sl2,l,apply(w, i -> {i}),0);
      r=conformalBlockRank(V);   
      if r!=1 then continue;
      Lemma52Examples = append(Lemma52Examples,{w,l});
      Tmc=Tminusc(w,l);
      if Tmc == apply(#Tmc, i -> {}) then continue;
      wprime=tableauContent(Tmc);
      Vprime=conformalBlockVectorBundle(sl2,l-1,apply(wprime, i -> {i}),0);
      rprime=conformalBlockRank(Vprime); 
      if rprime!=1 then error concatenate(toString({w,l}), " does not satisfy Lemma 5.2") << endl;
)))))))
#Lemma52Examples



---------------------------------
---------------------------------
-- Check some random n,w,l
---------------------------------
---------------------------------


time for i from 1 to 100000 do (
    n=random(4,12);
    l=random(1,10);    
    w=reverse sort apply(n, i -> random(1,l));
    if odd sum(w) then continue;
    V=conformalBlockVectorBundle(sl2,l,apply(w, i -> {i}),0);
    r=conformalBlockRank(V);   
    if r!=1 then continue;
    Lemma52Examples = append(Lemma52Examples,{w,l});
    Tmc=Tminusc(w,l);
    if Tmc == apply(#Tmc, i -> {}) then continue;
    wprime=tableauContent(Tmc);
    Vprime=conformalBlockVectorBundle(sl2,l-1,apply(wprime, i -> {i}),0);
    rprime=conformalBlockRank(Vprime); 
    if rprime!=1 then error concatenate(toString({w,l}), " does not satisfy Lemma 5.2") << endl;
)
#(unique Lemma52Examples)
-- checked 1492 unique examples of Lemma 5.2 in 477 seconds on August 29, 2016



