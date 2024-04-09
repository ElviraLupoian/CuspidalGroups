// this function computes the cuspidal group CH(p) of the modular curve XH(p) 
// we input a prime p and the k = the index of H in (Z/pZ)*
// the output is the cuspidal group 

cuspidalgroupXHp := function(p,k) ;

s := [ a : a in [2..p-1] ] ;
t := [ [b^i : i in [0..p-2] ] : b in s] ; 
tt := [ [ a mod p : a in b] : b in t] ;
kk := [ #Set(c) : c in tt];
ind := [ i : i in [1..#kk] |  kk[i] eq (p-1) ] ;
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

t := s/k ;
t := Integers() ! t;


Ords1 := [] ;

for i in [0..k-1] do;
oo := [] ;
for j in [0..k-1] do ;
oo[j+1] := &+[  (p/2)*B2((a^(i+j + m*k))/p) : m in [0..t-1] ] - p*(t)*(1/12);
end for;
for j in [0..k-1] do ;
oo[ k + j+1] := t/12 - &+[ p*(p/2)* B2((a^( k-1 +j + m*k))/p) : m in [0..t-1] ] ;
end for;
Ords1[i+1] := oo ;
end for ;

Ords2 := [] ;

for i in [1..k-2] do;
oo := [] ;
for j in [0..k-1] do ;
oo[j+1] := 0 ;
end for;
for j in [0..k-1] do ;
oo[ k+ j+1] :=  &+[  (p/2)*B2((a^(i+j + m*k))/p) : m in [0..t-1] ]  -  &+[  (p/2)*B2((a^ (k-1+j + m*k))/p) : m in [0..t-1] ] ;
end for;
Ords2[i] := oo ;
end for ;


GG := GCD([12, t]);
GGG := 12/GG ;
GGG := Integers() ! GGG;
R := LCM([2, GGG]) ;

o := [];


for j in [0..k-1] do ;
o[j+1 + k ] := &+ [ R*(p/2)*B2((a^(k-1 +j + m*k))/p) : m in [0..t-1] ] ;
end for ;

for j in [0..k-1] do ;
o[  j + 1] :=  R*(t/12) ;
end for;

Ords2[k-1] := o;
Z := FreeAbelianGroup(2*k) ;
T := sub<Z| [ Z.i - Z.(2*k) : i in [1..2*k-1] ]>;

Ords1 := [ [ Integers() ! a : a in b ] : b in Ords1 ];
rel1 := [ &+[a[i]*Z.i : i in [1..2*k] ] : a in Ords1 ];

Ords2 := [ [ Integers() ! a : a in b ] : b in Ords2 ];
rel2 := [ &+[a[i]*Z.i : i in [1..2*k] ] : a in Ords2 ];
rel := rel1 cat rel2;
CS := quo< T | rel >;
return CS;
end function ;
