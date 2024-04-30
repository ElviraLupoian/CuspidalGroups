// this computes the two rational cuspidal subgroups of XHp, for p in the list  stated
// the output is the list < p, k, CH^{inf} (p), CH(Q)(p) > 

P := [13, 17] ; // we input a list of primes, in the thesis this was PrimesInInterval(11,100) ;
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


for i in [1..n] do;
p := P[i] ;
a := M[i] ;

b := p mod 12;
b := Integers() ! b;
bb := a^(2*(p-2));

s := (1/2)*(p-1) ;
s := Integers() ! s;

K := [ k : k in [2..s-1] | s mod k eq 0 ]; 


B2 := function(x) ;
t := x - Floor(x) ;
return t^2 -t +1/6;
end function; 

for k in K do;

t := s/k ;
t := Integers() ! t;


Ords1 := [] ;

for i in [0..k-1] do;
oo := [] ;
for j in [0..k-1] do ;
oo[j+1] := &+[  (p/2)*B2((a^(i+j + m*k))/p) : m in [0..t-1] ] -  &+[  (p/2)*B2((a^(k-1+j + m*k))/p) : m in [0..t-1] ];
end for;
for j in [0..k-1] do ;
oo[k+j+1] := 0;
end for ;
Ords1[i+1] := oo ;
end for ;

Z := FreeAbelianGroup(2*k) ;
T := sub<Z| [ Z.i - Z.(k) : i in [1..k-1] ] >;

Ords1 := [ [ Integers() ! a : a in b ] : b in Ords1 ];
rel1 := [ &+[a[i]*Z.i : i in [1..k] ] : a in Ords1 ];


rel := rel1;

CS1 := quo< T | rel >;

GG := GCD([12, t]);
GGG := 12/GG ;
GGG := Integers() ! GGG;
R := LCM([2, GGG]) ;

o := [];


for j in [0..k-1] do ;
o[j+1  ] := &+ [ R*(p/2)*B2((a^(k-1 +j + m*k))/p) : m in [0..t-1] ] ;
end for ;

for j in [0..k-1] do ;
o[  j + 1 +k ] :=  R*(t/12) ;
end for;

Ords1[k] := o;

gg1 := &+[ Z.i : i in [1..k] ] ;
gg2 := &+[ Z.i : i in [k+1..2*k] ] ;
T := sub<Z| [ Z.i - Z.k : i in [1..k-1] ] cat [ gg1 - gg2] >;
Ords1 := [ [ Integers() ! a : a in b ] : b in Ords1 ];
rel1 := [ &+[a[i]*Z.i : i in [1..2*k] ] : a in Ords1 ];

rel := rel1;

CS2 := quo< T | rel >;
<p,k,CS1, CS2>;

end for ;
end for;
