// this function computes the rational cuspidal group C1(p)(Q) of X1(p) 
// we input a prime p (at least 11)
// output is the rational cuspidal group 

rationalcuspidalgroupX1p := function(p) ;
s := [ a : a in [2..p-1] ] ;
t := [ [b^i : i in [0..p-2] ] : b in s] ; 
tt := [ [ a mod p : a in b] : b in t] ;
k := [ #Set(c) : c in tt];
ind := [ i : i in [1..#k] |  k[i] eq (p-1) ] ;
t := ind[1] ;
a := s[t] ;
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
 return CS;
end function ;

