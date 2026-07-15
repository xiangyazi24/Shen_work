LoadPackage("transgrp");;
SetPrintFormattingStatus("*stdout*", false);;

F := GF(2);;
H := TransitiveGroup(12,90);;
S12 := SymmetricGroup(12);;
N := Normalizer(S12,H);;

Rows := B -> List([1..Length(B)], i -> B[i]);;
Supp := v -> Set(Filtered([1..12], i -> v[i] <> Zero(F)));;

Code := function(B)
  if Length(B)=0 then return [ [] ]; fi;
  return Set(List(Elements(VectorSpace(F,Rows(B))), Supp));
end;;

WeightEnum := function(B)
  local out,v,w;
  out := List([0..12],i->0);
  if Length(B)=0 then out[1]:=1; return out; fi;
  for v in Elements(VectorSpace(F,Rows(B))) do
    w := Length(Supp(v));
    out[w+1] := out[w+1]+1;
  od;
  return out;
end;;

RadDim := function(B)
  if Length(B)=0 then return 0; fi;
  return Length(B)-RankMat(B*TransposedMat(B));
end;;

LiftTop := function(h)
  local img,i;
  img := [1..24];
  for i in [1..12] do
    img[2*i-1] := 2*(i^h)-1;
    img[2*i] := 2*(i^h);
  od;
  return PermList(img);
end;;

FlipPerm := function(v)
  local img,i;
  img := [1..24];
  for i in [1..12] do
    if v[i] <> Zero(F) then
      img[2*i-1] := 2*i;
      img[2*i] := 2*i-1;
    fi;
  od;
  return PermList(img);
end;;

SplitGroup := function(B)
  local gens;
  gens := List(Rows(B),FlipPerm);
  Append(gens,List(GeneratorsOfGroup(H),LiftTop));
  return Group(gens);
end;;

OnCodes := function(C,g)
  return Set(List(C,A->OnSets(A,g)));
end;;

subs := MTX.BasesSubmodules(PermutationGModule(H,F));;
recs := [];;
Print("HEADER|HORDER=",Size(H),"|NORDER=",Size(N),"|SUBS=",Length(subs),"\n");

for i in [1..Length(subs)] do
  B := subs[i];
  C := Code(B);
  if Length(B)=0 then
    tid := 0;
  else
    G := SplitGroup(B);
    tid := TransitiveIdentification(G);
  fi;
  r := rec(idx:=i,dim:=Length(B),we:=WeightEnum(B),rad:=RadDim(B),tid:=tid,code:=C);
  Add(recs,r);
  Print("MODULE|IDX=",i,"|DIM=",r.dim,"|RAD=",r.rad,"|TID=",r.tid,"|WE=",r.we,"\n");
od;

Print("DIMENSIONS|",Collected(List(recs,r->r.dim)),"\n");

# Exact normalizer-orbit classification of every labeled invariant code.
todo := [1..Length(recs)];;
orbno := 0;;
while Length(todo)>0 do
  i := todo[1];
  orb := Orbit(N,recs[i].code,OnCodes);
  members := Filtered(todo,j->recs[j].code in orb);
  orbno := orbno+1;
  tids := Set(List(members,j->recs[j].tid));
  Print("ORBIT|NO=",orbno,"|REP=",i,"|DIM=",recs[i].dim,"|RAD=",recs[i].rad,
        "|TIDS=",tids,"|COUNT=",Length(members),"|INDICES=",members,
        "|WE=",recs[i].we,"\n");
  todo := Filtered(todo,j->not j in members);
od;

# Locate the three canonical matching-code modules and their adjacent ladder.
PairWE5 := [1,0,0,0,15,0,0,0,15,0,0,0,1];;
PairWE6 := [1,0,6,0,15,0,20,0,15,0,6,0,1];;
PairWE7 := [1,0,6,0,15,0,84,0,15,0,6,0,1];;
for target in [PairWE5,PairWE6,PairWE7] do
  hits := Filtered(recs,r->r.we=target);
  Print("PAIR_LADDER|DIM=",hits[1].dim,"|COUNT=",Length(hits),
        "|TIDS=",Set(List(hits,r->r.tid)),"|RAD=",Set(List(hits,r->r.rad)),
        "|INDICES=",List(hits,r->r.idx),"|WE=",target,"\n");
od;

QUIT;
