// this code is used to compare the rational cuspidal subgroup of X1(p) to the  entire rationl torsion subgroup of the Jacobian 
// the output is < prime, size of the cuspidal group, bound on the torsion subgroup of the Jacobian>
P := PrimesInInterval(11,83) ;

M := [] ;
GPR := [] ;
Kers := [] ;



for i in [1..#P] do ;
p := P[i] ;
s := [ a : a in [2..p-1] ] ;
t := [ [b^i : i in [0..p-2] ] : b in s] ; 
tt := [ [ a mod p : a in b] : b in t] ;
k := [ #Set(c) : c in tt];
ind := [ i : i in [1..#k] |  k[i] eq (p-1) ] ;
t := ind[1] ;
M[i] := s[t] ;
end for;



P := Eltseq(P) ;
n := #P ;


for i in [1..n] do ;
p := P[i] ;
a := M[i];
J := JOne(p) ;
torsbound := TorsionMultiple(J) ;

b := p mod 12;
b := Integers() ! b;
bb := a^(2*(p-2));

s := (1/2)*(p-1) ;
s := Integers() ! s;




B2 := function(x) ;
t := x - Floor(x) ;
return t^2 -t +1/6;
end function; 

Ords1 := [] ;

for i in [1..s-2] do;
oo := [] ;
for j in [0..s-1] do ;
oo[j+1] := (p/2)*B2((a^(i-1+j))/p) + (p/2)*(bb)*B2((a^(i +1 + j))/p)  - (bb +1)*(p/2)*B2((a^(i+j))/p) ;
end for;
Ords1[i] := oo ;
end for ;

oo2 := [];
for j in [0..s-1] do ;
T :=  B2(a^(s-2+j)/p) - B2(a^(s-1+j)/p)  ;
T := (p^2)*(1/2)*T ;
oo2[j+1] := T ;
end for ;


Ords1[s-1] := oo2 ;

Z := FreeAbelianGroup(s) ;
T := sub<Z| [ Z.i - Z.(s) : i in [1..s-1] ]>;
Ords1 := [ [ Integers() ! a : a in b ] : b in Ords1 ];
rel1 := [ &+[a[i]*Z.i : i in [1..s] ] : a in Ords1 ];
CS := quo< T | rel1 >;

<p, #CS, torsbound>;
end for ;
