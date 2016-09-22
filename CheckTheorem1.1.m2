# Quantum-Kostka-RankOne
The following various .m2 files with programs for algorithms described in Quanum Kostka and the rank on problem for sl_2m. 

{*
Updated July 14, 2016

Goal: check Theorem 1.1 (classification theorem) in the July 13, 2016 draft

*}


loadPackage("ConformalBlocks");
sl2=simpleLieAlgebra("A",1);

isMaximal = (w,l) -> (
    -- l maximal?
    T:=tally(w);
    Tl:=if T#?l then T#l else 0;    
    if Tl >= #w-3 then return true;
    -- sum maximal?
    m:=0;
    if even(n) then m=lift(n/2,ZZ) else m=lift((n-1)/2,ZZ);
    if sum(w) == 2*m*l then return true;
    return false
);

checkTheorem11 = (w,l) -> (
    s:=lift(sum(w)/2,ZZ);
    p:=s % l;
    k:=lift( (s-p)/l,ZZ);
    if p==0 then (
        p=l;
	k=k-1
    );
    Lambda:=sum drop(w, {0,2*k});
    V:=conformalBlockVectorBundle(sl2,l,apply(w, i -> {i}),0);
    r:=conformalBlockRank(V);   
    if Lambda < p and r > 0 then return false;
    if Lambda == p and r != 1 then return false;
    if Lambda > p and not isMaximal(w,l) and r <= 1 then return false;
    if Lambda > p and isMaximal(w,l) and r != 1 then return false;
    return true
);

end
load "CheckTheorem1.1.m2"

-----------------------------------
-----------------------------------
-- Check main theorem
-----------------------------------
-----------------------------------

-- Check all small levels for n=5
Theorem11Examples = {};
n=5;
time for l from 1 to 10 do (
 for i1 from 1 to l do (
  for i2 from 1 to i1 do (
   for i3 from 1 to i2 do (
    for i4 from 1 to i3 do (
     for i5 from 1 to i4 do (
      w=reverse sort {i1,i2,i3,i4,i5};    
      if odd(sum(w)) then continue;
      Theorem11Examples = append(Theorem11Examples,{w,l});
      if checkTheorem11(w,l) == false then error concatenate(toString({w,l})," contradicts Theorem 1.1") << endl;
))))))
#Theorem11Examples 

n=6;
time for l from 1 to 10 do (
 for i1 from 1 to l do (
  for i2 from 1 to i1 do (
   for i3 from 1 to i2 do (
    for i4 from 1 to i3 do (
     for i5 from 1 to i4 do (
      for i6 from 1 to i5 do (
      w=reverse sort {i1,i2,i3,i4,i5,i6};    
      if odd(sum(w)) then continue;
      Theorem11Examples = append(Theorem11Examples,{w,l});
      if checkTheorem11(w,l) == false then error concatenate(toString({w,l})," contradicts Theorem 1.1") << endl;
)))))))
#Theorem11Examples 



time for i from 1 to 100000 do (
    n=random(4,12);
    l=random(1,10);    
    w=reverse sort apply(n, i -> random(1,l));
    if odd sum(w) then continue;
    Theorem11Examples = append(Theorem11Examples,{w,l});
    if checkTheorem11(w,l) == false then error concatenate(toString({w,l})," contradicts Theorem 1.1") << endl;
)
#(unique Theorem11Examples)
-- checked 24,785 unique examples in 679.329 seconds on July 14, 2016

