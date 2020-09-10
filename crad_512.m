
/*
 The following parameters are hardcoded since they are used in a lot of functions and don't
 change throughout the code. Overall, the code is general enough that changing to a different
 prime p would not require too many changes. In case 9 does not divide p+1, the functions for
 3-isogenies are included as well.
*/

ells := [ 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 
     103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 
     223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 
     349, 353, 367, 373, 379, 383, 389 ];
p := 2^3*3*&*ells - 1;
F := GF(p);

/*
 The following are exponents such that exponentiation with them corresponds to computing
 a square, cube, quartic, fifth, seventh, ninth, eleventh and thirteenth root respectively.
*/

sq_exp := (p+1) div 4;
tri_exp := (2*p-1) div 3;
quart_exp := (p+1) div 8;
quint_exp := (3*p-2) div 5;
sept_exp := (4*p-3) div 7;
novem_exp := (5*p-4) div 9;
undecim_exp := (6*p-5) div 11;
tredecim_exp := (7*p-6) div 13;

/*
 We fix the bound for swapping to the O(sqrt(ell)) complexity formulas as 113, since this is the
 cut-off where they start outperforming the old Vélu-type formulas in Magma.
*/

degree_bound := 113;


function xDBL(P,A)
  v1:=P[1]+P[2];
  v1:=v1^2;
  v2:=P[1]-P[2];
  v2:=v2^2;
  x2:=v1*v2;
  v1:=v1-v2;
  v3:=(A+2)*v1/4;
  v3:=v3+v2;
  v3*:=v1;
  if v3 eq 0 then
    return [0,0];
  end if;
  return [x2/(v3),1];
end function;


function xADD(P,Q,PmQ,A)
  if P eq [0,0] then
    return Q;
  elif Q eq [0,0] then
    return P;
  elif PmQ eq [0,0] then
    return xDBL(P,A);
  end if;
  v0:=P[1]+P[2];
  v1:=Q[1]-Q[2];
  v1:=v1*v0;
  v0:=P[1]-P[2];
  v2:=Q[1]+Q[2];
  v2:=v2*v0;
  v3:=v1+v2;
  v3:=v3^2;
  v4:=v1-v2;
  v4:=v4^2;
  v4*:=PmQ[1];
  if v4 eq 0 then
    return [0,0];
  end if;
  return [v3/(v4),1];
end function;


function Ladder(m,x,A)
  if m eq 0 then
    return [0,0];
  end if;
  k:=Floor(Log(m)/Log(2));
  mtemp:=m-2^k;
  x0:=x;
  x1:=xDBL(x,A);
  for i in [1..(k)] do
    bin:=2^(k-i);
    if mtemp ge bin then
      x0:=xADD(x0,x1,x,A);
      x1:=xDBL(x1,A);
      mtemp-:=bin;
    else
      x1:=xADD(x0,x1,x,A);
      x0:=xDBL(x0,A);
    end if;
  end for;
  return x0,x1;
end function;


function SubProductTree(points,height)
  Q<x>:=PolynomialRing(Parent(points[1]));
  tree:=[Q!0 : i in [1..2^(height)]];
  for i in [1..#points] do
    tree[2^(height-1)-1+i]:=x-points[i];
  end for;
  for k in [1..(height-1)] do
    for i in [1..2^(height-1-k)] do
      index:=2^(height-1-k)-1+i;
      if tree[2*index+1] eq 0 and tree[2*index] ne 0 then
        tree[index]:=tree[2*index];
      else
        tree[index]:=tree[2*index]*tree[2*index+1];
      end if;
    end for;
  end for;
  return tree;
end function;


function SubProductTreePolynomials(polys,height)
  zero:=0*polys[1];
  tree:=[zero : i in [1..2^(height)]];
  for i in [1..#polys] do
    tree[2^(height-1)-1+i]:=polys[i];
  end for;
  for k in [1..(height-1)] do
    for i in [1..2^(height-1-k)] do
      index:=2^(height-1-k)-1+i;
      if tree[2*index+1] eq 0 and tree[2*index] ne 0 then
        tree[index]:=tree[2*index];
      else
        tree[index]:=tree[2*index]*tree[2*index+1];
      end if;
    end for;
  end for;
  return tree;
end function;


function MultipointEvaluation(points,tree,P,height)
  zero:=0*tree[1];
  tree_eval:=[zero: i in [1..#tree]];
  tree_eval[1]:= P mod tree[1];
  for k in [1..(height-1)] do
    for i in [1..2^k] do
      index:=2^k-1+i;
      if tree[index] eq 0 then
        tree_eval[index]:=0;
      else
        tree_eval[index]:=tree_eval[Floor(index/2)] mod tree[index];
      end if;
    end for;
  end for;
  eval_multipoint:=[Parent(points[1])!0: i in [1..#points]];
  for i in [1..#points] do
    eval_multipoint[i]:=Evaluate(tree_eval[2^(height-1)-1+i],points[i]);
  end for;
  return eval_multipoint;
end function;


function evaluate_isogeny_big_degree(isog,P,l)
	if P eq [0,0] then
		return [0,0];
	end if;
	v:=P[1];
	h1:=isog[1];p1:=isog[2];tree1:=isog[3];poly1:=isog[4];poly2:=isog[5];
	p3:=isog[6];poly4:=isog[7];
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,v)): poly3 in p3];
  poly3:=&*ptemp3;
  denom:=Evaluate(poly1,v)*Evaluate(poly2,v)*Evaluate(poly4,v)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  if denom eq 0 then
    return [0,0];
  end if;
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,1/v)): poly3 in p3];
  poly3:=&*ptemp3;
  num:=Evaluate(poly1,1/v)*Evaluate(poly2,1/v)*Evaluate(poly4,1/v)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  return [v^l*(num/denom)^2,1];
end function;


function kernel_generator_to_isogeny_big_degree(A0,P,l)
  _<o>:=PolynomialRing(Parent(A0));
  E0:=EllipticCurve(o^3+A0*o^2+o);
  m:=Floor(Sqrt(l/2));
  k:=Floor(m/2);
  if m^2+m ge Ceiling(l/2) then
    m:=m-1;
  end if;
  _<x>:=PolynomialRing(Parent(A0));
  _<y,T>:=PolynomialRing(Parent(A0),2);
  p1:=[P[1]];
  Ptemp:=P;
  Pdiff:=[0,0];
  Q:=Ladder(2*m,P,A0);
  Qtemp:=Q;
  Qdiff:=[0,0];
  Stemp:=Ladder(m,P,A0);
  Sdiff:=Stemp;
  p2:=[Q[1]-x];
  p3:=[(y-Q[1])^2*T^2 - T*2*(y+Q[1]+y*Q[1]*(2*A0+y+Q[1]))+(y*Q[1]-1)^2];
  p4:=[x-Stemp[1]];
  for i in [2..(m-1)] do
    Pttemp:=Ptemp;
    Ptemp:=xADD(Ptemp,P,Pdiff,A0);
    Pdiff:=Pttemp;
    Append(~p1,Ptemp[1]);
  end for;
  for i in [2..k] do
      Qttemp:=Qtemp;
      Qtemp:=xADD(Qtemp,Q,Qdiff,A0);
      Qdiff:=Qttemp;
      Sttemp:=Stemp;
      Stemp:=xADD(Stemp,Q,Sdiff,A0);
      Sdiff:=Sttemp;
    Append(~p2,(x-Qtemp[1]));
    Append(~p4,(x-Stemp[1]));
    Append(~p3,(y-Qtemp[1])^2*T^2 - T*2*(y+Qtemp[1]+y*Qtemp[1]*(2*A0+y+Qtemp[1]))+(y*Qtemp[1]-1)^2);
  end for;
  R:=Ladder(2*k*m+m,P,A0);
  Rdiff:=Ladder(2*k*m+m-1,P,A0);
  Append(~p4,x-R[1]);
  Rtemp:=R;
  for i in [(2*k*m+m+1)..Floor(l/2)] do
    Rttemp:=Rtemp;
    Rtemp:=xADD(Rtemp,P,Rdiff,A0);
    Rdiff:=Rttemp;
    Append(~p4,(x-Rtemp[1]));
  end for;
  h1:=Ceiling(Log(#p1)/Log(2))+1;
  h2:=Ceiling(Log(#p2)/Log(2))+1;
  h3:=Ceiling(Log(#p3)/Log(2))+1;
  h4:=1+Ceiling(Log(#p4)/Log(2))+1;

  tree1:=SubProductTree(p1,h1);
  tree2:=SubProductTreePolynomials(p2,h2);
  tree4:=SubProductTreePolynomials(p4,h4);
  
  poly1:=tree1[1];poly2:=tree2[1];poly4:=tree4[1];
  isogeny:=<h1,p1,tree1,poly1,poly2,p3,poly4>;
  a:=A0+2;
  d:=A0-2;
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,1)): poly3 in p3];
  poly3:=&*ptemp3;
  prod3:=Evaluate(poly1,1)*Evaluate(poly2,1)*Evaluate(poly4,1)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  ptemp3:=[UnivariatePolynomial(Evaluate(poly3,2,-1)): poly3 in p3];
  poly3:=&*ptemp3;
  prod4:=Evaluate(poly1,-1)*Evaluate(poly2,-1)*Evaluate(poly4,-1)*(&*MultipointEvaluation(p1,tree1,poly3,h1));
  a1:=a^(l)*prod4^8;
  d1:=d^(l)*prod3^8;
  A:=2*(a1+d1)/(a1-d1);
  return A,isogeny;
end function;


function step_zero_Montgomery(X1, Z1, X2, Z2, X3, Z3, A)
  return (X2^2-Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2+Z2^2), 4*(X2*X3-Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1;
end function;


function step_one_Montgomery(X1, Z1, X3, Z3, X2, Z2, A)
  return 4*(X2*X3-Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1, (X2^2-Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2+Z2^2);
end function;


function scalar_multiplication_Montgomery(n, X1, Z1, A)
  X2 := 1; Z2 := 0; X3 := X1; Z3 := Z1;
  nbits := Reverse(Intseq(n,2));
  if Z1 eq 0 then return "Error";
  else for i := 1 to #nbits do
    if nbits[i] eq 0 then X2, Z2, X3, Z3 := step_zero_Montgomery(X1, Z1, X2, Z2, X3, Z3, A);
    else X2, Z2, X3, Z3 := step_one_Montgomery(X1, Z1, X2, Z2, X3, Z3, A);
    end if;
  end for;
  return X2, Z2;
  end if;
end function;


function differential_addition_Montgomery(X1, Z1, X2, Z2, X3, Z3, A)
  if X1 eq 0 or Z1 eq 0 or [X2,Z2] eq [0,0] or [X3,Z3] eq [0,0] then return 0, 0;
  else
    return 4*(X2*X3-Z2*Z3)^2*Z1, 4*(X2*Z3-Z2*X3)^2*X1;
  end if;
end function;


function double_point_Montgomery(X2, Z2, A)
  if Z2 eq 0 or X2^3+A*X2^2+X2 eq 0 then return 0, 0;
  else return (X2^2-Z2^2)^2, 4*X2*Z2*(X2^2+A*X2*Z2+Z2^2);
  end if;
end function;


function find_torsion_point(A,ell)
  F:=Parent(A);
  fac:=(p+1) div ell;
  repeat
    xP := Random(F);
    twist := not IsSquare(xP^3+A*xP^2+xP); if twist then A := -A; xP := -xP; end if;
    zP:=F!1;
    Xl,Zl:=scalar_multiplication_Montgomery(fac,xP,zP,A);
  until Zl ne 0;
  return twist,Xl,Zl;
end function;


function act_with_small_ell_on_Montgomery(A, ell, xTors, xPush)

  /*
   This function computes an ell-isogeny, where xTors represents an ell-torsion point's
   x-coordinate, and xPush represents an x-coordinate of a point for which we also want
   to compute the image. We start from a Montgomery coefficient and end up at a new
   Montgomery coefficient. These are the classical CSIDH formulas.
  */

  XQ := xTors; ZQ := 1;
  pi := XQ; sigma := XQ - 1/XQ;
  fXPush := (XQ*xPush-1); fZPush := (xPush-XQ);
  if ell eq 3 then return pi^2*(A-6*sigma), xPush*fXPush^2, fZPush^2;
  else
  XQ, ZQ := double_point_Montgomery(XQ, ZQ, A); xQ := XQ/ZQ;
  pi *:= xQ; sigma +:= xQ - 1/xQ;
  fXPush *:= (xQ*xPush-1); fZPush *:= (xPush-xQ);
  XPrev := xTors; ZPrev := 1;
  for i in [3..(ell-1) div 2] do
    XTemp := XQ; ZTemp := ZQ;
    XQ, ZQ := differential_addition_Montgomery(XPrev, ZPrev, xTors, 1, XQ, ZQ, A); xQ := XQ/ZQ;
    pi *:= xQ; sigma +:= xQ - 1/xQ;
    fXPush *:= (xQ*xPush-1); fZPush *:= (xPush-xQ);
    XPrev := XTemp; ZPrev := ZTemp;
  end for;
  end if;
  return pi^2*(A - 6*sigma), xPush*fXPush^2, fZPush^2;
end function;


function act_with_big_ell_on_Montgomery(A, ell, xTors, xPush)

  /*
   This function computes an ell-isogeny, where xTors represents an ell-torsion point's
   x-coordinate, and xPush represents an x-coordinate of a point for which we also want
   to compute the image. We start from a Montgomery coefficient and end up at a new
   Montgomery coefficient. The formulas from Bernstein et al are used with complexity
   O(sqrt(ell)).
  */

  F:=Parent(xTors);
  Af,isog:=kernel_generator_to_isogeny_big_degree(A,[xTors,F!1],ell);
  fXpush:=evaluate_isogeny_big_degree(isog,[xPush,F!1],ell);
  return Af,fXpush[1],fXpush[2];
end function;


function act_with_ell_on_Montgomery(A, ell, xTors, xPush, degree_bound)

  /*
   This is just a helper function to differentiate between the classical CSIDH formulas
   to compute an ell-isogeny, and the new ones from Bernstein et al that have a better
   asymptotic complexity. The cut-off for swapping to the newer formulas is ell > degree_bound.
  */

  if ell le degree_bound then
    return act_with_small_ell_on_Montgomery(A, ell, xTors, xPush);
  else
    return act_with_big_ell_on_Montgomery(A, ell, xTors, xPush);
  end if;
end function;


function Montgomery_min_to_Montgomery(A)

  /*
   This function takes a Montgomery^- coefficient on the surface and gives the
   corresponding Montgomery coefficient on the floor obtained from the 2-isogeny
   with kernel <(0,0)>. Montgomery^- coefficients represent an elliptic curve of
   the form y^2 = x^3+A*x^2-x.
  */

  return -2*A/((A^2+4)^sq_exp);
end function;


function Montgomery_to_Montgomery_min(A)

  /*
   This function takes a Montgomery coefficient on the floor and gives the
   corresponding Montgomery^- coefficient on the surface obtained from the 2-isogeny
   with kernel <(0,0)>. Montgomery^- coefficients represent an elliptic curve of
   the form y^2 = x^3+A*x^2-x.
  */

  return -2*A/((4-A^2)^sq_exp);
end function;


function Montgomery_to_Tate(A, xP : ell_eq_three := false)

  /*
   This function takes a Montgomery coefficient A and calculates the corresponding
   Tate normal form y^2 + M*xy + N*y = x^3 + Nx*^2, which is obtained by an isomorphism
   that puts a point with x-coordinate xP at (0,0), where xP is assumed to be an ell-
   torsion point's x-coordinate. The choice of sign for the y-coordinate corresponding
   to xP is arbitrary but fixed. Note that in classical notation, M = 1-c and N = -b.
   The case ell=3 is also included. This is not a Tate form but close to it, in which
   case the curve has the form y^2 + M*xy + N*y = x^3 (so no quadratic term in x).
   We use the general naming conventions [u,r,s,t] for Weierstrass-isomorphisms.
  */

  r := xP;
  t := (r*(1+r*(A+r)))^sq_exp;
  twot_inv := 1/(2*t);
  s := (1+r*(2*A+3*r))*twot_inv;
  if not ell_eq_three then
    u_inv := (A+3*r-s^2)*twot_inv;
  else
    u_inv := 1;
  end if;
  M := 2*s*u_inv;
  N := 2*t*u_inv^3;
  return M, N;
end function;


function Weier_to_Montgomery(coeffs)

  /*
   This function takes a 5-tuple [a1,a2,a3,a4,a6] of a (long) Weierstrass form and
   calculates the corresponding Montgomery coefficient.
   Note that not all curves have a Montgomery representation, and we just assume
   the input does have one.
   Furthermore, even if the curve has a Montgomery form, the formulas only work for
   the case where the rational 2-torsion of the curve is Z/2Z. The reason is that
   this allows us to solve a cubic polynomial without using field extensions (i.e.
   we need to avoid casus irreducibilis for the cubic polynomial). In particular,
   for CSIDH, this means the computations need to be done on curves on the floor.
  */

  a1 := coeffs[1]; a2 := coeffs[2]; a3 := coeffs[3];
  a4 := coeffs[4]; a6 := coeffs[5];
  s := -a1/2;
  B := (a1^2/4 + a2);
  C := (a1*a3/2 + a4);
  D := a3^2/4 + a6;
  delta0 := B^2-3*C;
  delta1 := B*(2*B^2-9*C)+27*D;
  squareroot := (delta1^2-4*delta0^3)^sq_exp;
  cuberoot := ((delta1+squareroot)/2)^tri_exp;
  r := -(B+cuberoot+delta0/cuberoot)/3;
  t := -(a3+r*a1)/2;
  u2 := (a4-s*a3+2*r*a2-(t+r*s)*a1+3*r^2-2*s*t)^sq_exp;
  A := (a2-s*a1+3*r-s^2)/u2;
  return A;
end function;


function Montgomery_min_to_Tate_four(A, r, t)
  
  /*
   This functions transforms a Montgomery^- coefficient A to the coefficients of a Tate
   normal form of X1(4). A Montgomery^- coefficient A represents an elliptic curve of the
   form y^2 = x^3+A*x^2-x. The output M,N represents a curve of the form y^2 + M*xy + N*y
   = x^3 + N*x^2, and in this case for X1(4), M = 1 will always hold.
   Note that [r,t] is the Fp-rational 4-torsion point such that the isogeny with kernel
   2*[r,t] maps [r,t] to a 2-torsion point that has Fp-rational halves as well.
  */

  twot_inv := 1/(2*t);
  s := (-1+r*(2*A+3*r))*twot_inv;
  u_inv := (A+3*r-s^2)*twot_inv;
  M := 2*s*u_inv;
  N := 2*t*u_inv^3;
  return M, N;
end function;


function Tate_four_to_Montgomery_min(A)

  /*
   This function transforms a coefficient A representing a Tate normal form y^2 + x*y + A*y =
   x^3 + A*x^2 to Montgomery^- coefficient.
   B is a Montgomery coefficient on the surface where we simply translated 2*(0,0) = (-A,0) to (0,0).
   The rest is a classical rescaling to obtain a Montgomery^- coefficient (just as in CSURF).
  */

  B := 1/(4*A) - 2;
  eps := (B^2 - 4)^sq_exp;
  return (-B+3*eps)/((eps*(B-eps)*2)^sq_exp);
end function;


function sample_ell_torsion_point_Montgomery(A, ell)

  /*
   This function samples an ell-torsion point on an elliptic curve with Montgomery coefficient
   A for odd ell. If ell is not prime, a proper ell-torsion point is generated (i.e. it is not
   an m-torsion point for any m | d with 1 < m < ell).
  */

  repeat
  possible_torsion := [];
  repeat xP := Random(F); until IsSquare(((xP+A)*xP+1)*xP);
  XQ, ZQ := scalar_multiplication_Montgomery((p+1) div ell, xP, 1, A);
  if ZQ ne 0 then
    proper := true;
    for d in Divisors(ell) do
      if d ne 1 and d ne ell and proper then
        XR, ZR := scalar_multiplication_Montgomery(d, XQ, ZQ, A);
        if ZR eq 0 then proper := false; end if;
      end if;
    end for;
    if proper then possible_torsion cat:= [XQ, ZQ]; end if;
  end if;
  until possible_torsion ne [];
  return possible_torsion[1]/possible_torsion[2];
end function;


function three_iso(A, B)

  /*
   Given A, B representing an elliptic curve y^2 + A*x*y + B*y = x^3, return the coefficients
   newA, newB representing y^2 + newA*x*y + newB*y = x^3 obtained from the 3-isogeny with
   kernel <(0,0)>.
   Note that this function is not used in this implementation since 9 | p+1, so we can use
   faster 9-isogenies.
  */

  C := B^tri_exp; AC := A*C;
  newA := A-6*C; newB := A*AC - 3*AC*C + 9*B;
  return newA, newB;
end function;


function four_iso(A)

  /*
   Given the parameter A representing an element of X1(4) in Tate normal form with
   (0,0) as 4-torsion point, return the parameter newA representing the Tate normal
   form that is obtained from the isogeny with kernel <(0,0)>.
   The Tate normal coefficient A represents a curve of the form y^2 + x*y + A*y =
   x^3 + A*x^2.
  */

  C := A^quart_exp; C4 := 4*C; C42 := C4*C;
  newA := -C*(C42+1)/(C42-C4+1)^2;
  return newA;
end function;


function five_iso(A)

  /*
   Given the parameter A representing an element of X1(5) in Tate normal form with
   (0,0) as 5-torsion point, return the parameter newA representing the Tate normal
   form that is obtained from the isogeny with kernel <(0,0)>.
   The Tate normal coefficient A represents a curve of the form y^2 + (-A + 1)*x*y -
   A*y = x^3 - A*x^2.
  */

  C := A^quint_exp; C2 := C^2; C3 := C^3; C4 := C2^2;
  newA := C + 5*(C4+C2)/(C4-2*C3+4*C2-3*C+1);
  return newA;
end function;


function seven_iso(A)

  /*
   Given the parameter A representing an element of X1(7) in Tate normal form with
   (0,0) as 7-torsion point, return the parameter newA representing the Tate normal
   form that is obtained from the isogeny with kernel <(0,0)>.
   The Tate normal coefficient A represents a curve of the form y^2 + (-A^2 + A + 1)*x*y
   + (-A^3 + A^2)*y = x^3 + (-A^3 + A^2)*x^2, which is obtained from:
   http://math.mit.edu/~drew/X1_optcurves.html
  */

  A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4;
  inv := 1/(A5 - 8*A4 + 5*A3 + A2);
  C := (A5-A4)^sept_exp;
  newA := ((((((-7*C - 7)*C + (4*A2 - 12*A + 2))*C + (A3 - 10*A2 +
        4*A))*C + (-5*A3 + A2 + A))*C + (3*A4 - 9*A3 + 5*A2))*C
        + (3*A5 - 16*A4 + 12*A3))*inv;
  return newA;
end function;


function nine_iso(A);

  /*
   Given the parameter A representing an element of X1(9) in Tate normal form with
   (0,0) as 9-torsion point, return the parameter newA representing the Tate normal
   form that is obtained from the isogeny with kernel <(0,0)>.
   The Tate normal coefficient A represents a curve of the form y^2 + (-A^3 + A^2 + 1)*x*y
   + (-A^5 + 2*A^4 - 2*A^3 + A^2)*y = x^3 + (-A^5 + 2*A^4 - 2*A^3 + A^2)*x^2, which is
   obtained from: http://math.mit.edu/~drew/X1_optcurves.html
  */

  A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
  A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
  A12 := A6^2;
  C := ((A5-A4)*(A2-A+1)^3)^novem_exp;
  inv := 1/((A3-A2+A)^3*(A3-6*A2+3*A+1));
  newA := inv*(((((((((2*A2 - 5*A + 2)*C + (-A3 - 1))*C + (-3*A4 + 3*A3 - 3*A2))*C + (A6 - 6*A5 + 8*A4 - 8*A3 + 3*A2 - A))*C + 
    (2*A7 - 8*A6 + 14*A5 - 16*A4 + 10*A3 - 4*A2))*C + (A8 - 6*A7 + 12*A6 - 16*A5 + 12*A4 - 6*A3 + A2))*C 
    + (-2*A9 + 3*A8 - 3*A7 - A6 + 3*A5 - 3*A4 + A3))*C + (-2*A10 + 7*A9 - 15*A8 + 20*A7 - 19*A6 + 12*A5 - 
    5*A4 + A3))*C + 2*A12 - 14*A11 + 41*A10 - 77*A9 + 98*A8 - 89*A7 + 56*A6 - 23*A5 + 5*A4);
return newA;
end function;



function eleven_iso(A, B)

  /*
   Given the parameters A, B representing an element of X1(11) in Tate normal form with
   (0,0) as 11-torsion point, return the parameters newA, newB representing the Tate normal
   form that is obtained from the isogeny with kernel <(0,0)>.
   The Tate normal coefficients A, B represent a curve of the form y^2 + ((A^2 - A)*B + 1)*x*y
   + ((-A^5 + A^4 - A^3 + 2*A^2 - A)*B - A^4 + A^3)*y = x^3 + ((-A^5 + A^4 - A^3 + 2*A^2 - A)*B
   - A^4 + A^3)*x^2, with B^2 + (A^2 + 1)*B + A = 0, which is obtained from:
   http://math.mit.edu/~drew/X1_optcurves.html
  */

  A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
  A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
  A12 := A6^2; A13 := A*A12; A14 := A7^2; A15 := A*A14;
  A16 := A8^2; A17 := A*A16; A18 := A9^2; A19 := A*A18;
  A20 := A10^2; A21 := A*A20;
  denomnewB := 1/(A17 - 6*A16 - 15*A15 + 158*A14 - 194*A13 - 778*A12
    + 2777*A11 - 3640*A10 + 2088*A9 - 106*A8 - 437*A7 + 150*A6
    + 11*A5 - 10*A4 + A3);
  denomnewA := (A5 - A4 - 15*A3 + 14*A2 + 3*A - 1)*denomnewB;
  C := (A*(B*(1-A)*(A*B+1))^3)^undecim_exp;

  newA := denomnewA*(((((((((((
    -3*A14 - 12*A13 - 16*A12 - 37*A11 + 40*A10 - 33*A9 + 158*A8 - 128*A7 + 157*A6 - 184*A5 + 118*A4 - 80*A3 + 
    36*A2 - 10*A + 1)*B - 3*A16 - 12*A15 - 19*A14 - 46*A13 + 36*A12 - 57*A11 + 226*A10 - 202*A9 + 330*A8 -
    410*A7 + 349*A6 - 320*A5 + 215*A4 - 115*A3 + 46*A2 - 11*A + 1))*C + ((A14 - 9*A12 + A11 - 45*A10 +
    83*A9 - 97*A8 + 199*A7 - 221*A6 + 198*A5 - 186*A4 + 115*A3 - 53*A2 + 17*A - 2)*B + (A16 - 8*A14 - 54*A12 
    + 94*A11 - 144*A10 + 317*A9 - 388*A8 + 456*A7 - 512*A6 + 420*A5 - 301*A4 + 173*A3 - 70*A2 + 19*A - 2)))*C
    + ((-A13 - 5*A12 - 6*A11 - 5*A10 + 10*A9 + 24*A8 - 4*A7 + 20*A6 - 49*A5 + 30*A4 - 25*A3 + 13*A2 - 2*A)*B
    - A15 - 5*A14 - 7*A13 - 9*A12 + 9*A11 + 24*A10 + 7*A9 + 34*A8 - 74*A7 + 61*A6 - 82*A5 + 66*A4 - 36*A3 +
    15*A2 - 2*A))*C + ((2*A13 + 4*A12 - 6*A11 + 11*A10 - 48*A9 + 68*A8 - 83*A7 + 111*A6 - 96*A5 + 60*A4 -
    31*A3 + 9*A2 - A)*B + (2*A15 + 4*A14 - 4*A13 + 13*A12 - 58*A11 + 87*A10 - 140*A9 + 215*A8 - 228*A7 +
    211*A6 - 167*A5 + 95*A4 - 39*A3 + 10*A2 - A)))*C^3 + ((-3*A11 - A10 + 22*A9 - 42*A8 + 68*A7 - 103*A6 +
    100*A5 - 56*A4 + 17*A3 - 2*A2)*B - 3*A13 - A12 + 19*A11 - 40*A10 + 91*A9 - 170*A8 + 212*A7 - 201*A6 +
    149*A5 - 74*A4 + 20*A3 - 2*A2))*C + ((-3*A10 + 26*A8 - 51*A7 + 51*A6 - 45*A5 + 33*A4 - 12*A3 + A2)*B - 
    3*A12 + 23*A10 - 48*A9 + 77*A8 - 125*A7 + 140*A6 - 96*A5 + 42*A4 - 11*A3 + A2))*C + ((A11 - A10 -
    10*A9 + 26*A8 - 21*A7 + 4*A6 - 3*A5 + 7*A4 - 3*A3)*B + (A13 - A12 - 9*A11 + 24*A10 - 30*A9 + 42*A8 -
    61*A7 + 53*A6 - 24*A5 + 6*A4 - A3)))*C + ((A10 - 3*A9 - 6*A8 + 33*A7 - 47*A6 + 27*A5 - 4*A4 - A3)*B + 
    (A12 - 3*A11 - 7*A10 + 44*A9 - 85*A8 + 89*A7 - 57*A6 + 22*A5 - 4*A4)))*C + (2*A10 - 11*A9 + 21*A8 -
    14*A7 - 4*A6 + 9*A5 - 3*A4)*B + A12 - 2*A11 - 9*A10 + 38*A9 - 58*A8 + 46*A7 - 21*A6 + 6*A5 - A4);

  newB := denomnewB*(((((((((((((
    22*A18 + 132*A17 + 154*A16 + 11*A15 - 220*A14 - 1672*A13 + 1936*A12 - 3531*A11 + 8206*A10 - 9328*A9 +
    10384*A8 - 11286*A7 + 8426*A6 - 5170*A5 + 2618*A4 - 825*A3 + 154*A2 - 11*A)*B + (22*A20 + 132*A19 +
    176*A18 + 121*A17 - 198*A16 - 1793*A15 + 1815*A14 - 4983*A13 + 11605*A12 - 14806*A11 + 20856*A10 -
    25707*A9 + 24046*A8 - 20493*A7 + 14608*A6 - 7953*A5 + 3388*A4 - 990*A3 + 165*A2 - 11*A)))*C + ((-A19 -
    14*A18 - 31*A17 + 82*A16 + 125*A15 + 53*A14 + 291*A13 - 2176*A12 + 3433*A11 - 5944*A10 + 10232*A9 -
    11775*A8 + 11492*A7 - 10167*A6 + 6658*A5 - 3160*A4 + 1099*A3 - 217*A2 + 23*A - 1)*B - A21 - 14*A20 -
    32*A19 + 69*A18 + 108*A17 + 165*A16 + 321*A15 - 2264*A14 + 3795*A13 - 8378*A12 + 15614*A11 - 20687*A10 +
    25496*A9 - 27634*A8 + 23763*A7 - 17114*A6 + 10043*A5 - 4336*A4 + 1305*A3 - 240*A2 + 24*A - 1))*C +
    ((-6*A18 - 46*A17 - 70*A16 + 108*A15 + 170*A14 + 298*A13 - 4*A12 - 1846*A11 + 2810*A10 - 4788*A9 +
    8118*A8 - 8910*A7 + 7550*A6 - 5438*A5 + 2776*A4 - 862*A3 + 150*A2 - 10*A)*B - 6*A20 - 46*A19 - 76*A18 +
    68*A17 + 146*A16 + 470*A15 + 18*A14 - 1736*A13 + 2714*A12 - 6630*A11 + 12666*A10 - 16364*A9 + 18694*A8 -
    18416*A7 + 13990*A6 - 8226*A5 + 3608*A4 - 1024*A3 + 160*A2 - 10*A))*C + ((A18 - 4*A17 - 58*A16 - 49*A15 +
    215*A14 + 57*A13 + 315*A12 - 612*A11 - 1029*A10 + 2406*A9 - 3241*A8 + 4856*A7 - 5007*A6 + 3270*A5 -
    1519*A4 + 463*A3 - 68*A2 + 4*A)*B + (A20 - 4*A19 - 57*A18 - 54*A17 + 161*A16 + 67*A15 + 574*A14 - 825*A13
    - 755*A12 + 1788*A11 - 3943*A10 + 8278*A9 - 10627*A8 + 10314*A7 - 8332*A6 + 4974*A5 - 2013*A4 + 521*A3 -
    72*A2 + 4*A)))*C + ((9*A17 + 30*A16 - 90*A15 - 116*A14 + 356*A13 - 474*A12 + 1393*A11 - 2354*A10 +
    1671*A9 - 494*A8 - 217*A7 + 992*A6 - 1187*A5 + 608*A4 - 146*A3 + 20*A2 - A)*B + (9*A19 + 30*A18 - 81*A17
    - 95*A16 + 236*A15 - 491*A14 + 1886*A13 - 3313*A12 + 3509*A11 - 3598*A10 + 2740*A9 - 19*A8 - 2144*A7 +
    2436*A6 - 1692*A5 + 741*A4 - 174*A3 + 21*A2 - A)))*C + ((A17 + 21*A16 + 51*A15 - 173*A14 - 166*A13 +
    577*A12 - 882*A11 + 2457*A10 - 4247*A9 + 3988*A8 - 2661*A7 + 1501*A6 - 501*A5 + 11*A4 + 25*A3 - 2*A2)*B +
    (A19 + 21*A18 + 52*A17 - 153*A16 - 136*A15 + 354*A14 - 855*A13 + 3229*A12 - 5948*A11 + 7345*A10 - 8323*A9
    + 7759*A8 - 4851*A7 + 1885*A6 - 386*A5 - 12*A4 + 20*A3 - 2*A2)))*C + ((-4*A16 + 10*A15 + 109*A14 -
    213*A13 - 346*A12 + 1382*A11 - 2510*A10 + 4431*A9 - 6075*A8 + 5216*A7 - 2741*A6 + 924*A5 - 210*A4 + 28*A3
    - A2)*B - 4*A18 + 10*A17 + 105*A16 - 199*A15 - 247*A14 + 1056*A13 - 2629*A12 + 6262*A11 - 10306*A10 +
    11902*A9 - 10834*A8 + 7747*A7 - 3881*A6 + 1224*A5 - 229*A4 + 24*A3 - A2))*C + ((-3*A16 - 21*A15 + 28*A14
    + 239*A13 - 453*A12 - 519*A11 + 2620*A10 - 4457*A9 + 5256*A8 - 4654*A7 + 2783*A6 - 986*A5 + 184*A4 -
    18*A3 + A2)*B - 3*A18 - 21*A17 + 25*A16 + 221*A15 - 404*A14 - 311*A13 + 1911*A12 - 4468*A11 + 8501*A10 -
    11950*A9 + 11577*A8 - 7752*A7 + 3600*A6 - 1117*A5 + 212*A4 - 22*A3 + A2))*C + ((-7*A15 - 32*A14 + 86*A13
    + 288*A12 - 831*A11 - 166*A10 + 2804*A9 - 4384*A8 + 3555*A7 - 1804*A6 + 600*A5 - 118*A4 + 9*A3)*B - 7*A17
    - 32*A16 + 79*A15 + 263*A14 - 707*A13 - 47*A12 + 2010*A11 - 4202*A10 + 6387*A9 - 7326*A8 + 5600*A7 -
    2655*A6 + 743*A5 - 113*A4 + 7*A3))*C + ((3*A15 - 66*A13 + 31*A12 + 674*A11 - 1667*A10 + 1162*A9 + 816*A8
    - 1822*A7 + 1145*A6 - 302*A5 + 27*A4 - A3)*B + (3*A17 - 68*A15 + 83*A14 + 380*A13 - 1038*A12 + 637*A11 +
    1054*A10 - 2744*A9 + 3308*A8 - 2559*A7 + 1239*A6 - 335*A5 + 42*A4 - 2*A3)))*C + (4*A15 - 18*A14 + 73*A13 -
    204*A12 + 298*A11 - 188*A10 - 46*A9 + 170*A8 - 97*A7 - 34*A6 + 63*A5 - 22*A4 + A3)*B + 17*A16 + 6*A15 -
    314*A14 + 453*A13 + 1393*A12 - 5177*A11 + 6762*A10 - 3914*A9 + 300*A8 + 785*A7 - 362*A6 + 55*A5 - 4*A4);
  return newA, newB;
end function;





function thirteen_iso(A, B)

  /*
   Given the parameters A, B representing an element of X1(13) in Tate normal form with
   (0,0) as 13-torsion point, return the parameters newA, newB representing the Tate normal
   form that is obtained from the isogeny with kernel <(0,0)>.
   The Tate normal coefficients A, B represent a curve of the form y^2 + ((-A^4 - A^3 + A^2)/
   (A^2 + 2*A + 1)*B + (A^2 + A + 1)/(A + 1))*x*y + ((-A^7 - A^6 + A^5 - A^4 - 2*A^3 + A^2)/
   (A + 1)*B + (A^5 - A^3 + A^2))*y = x^3 + ((-A^7 - A^6 + A^5 - A^4 - 2*A^3 + A^2)/(A + 1)*B
   + (A^5 - A^3 + A^2))*x^2, with B^2 + (A^3 + A^2 + 1)*B - A^2 - A = 0, which is obtained from:
   http://math.mit.edu/~drew/X1_optcurves.html
  */

  A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
  A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
  A12 := A6^2; A13 := A*A12; A14 := A7^2; A15 := A*A14;
  A16 := A8^2; A17 := A*A16; A18 := A9^2; A19 := A*A18;
  A20 := A10^2; A21 := A*A20; A22 := A11^2; A23 := A*A22;
  A24 := A12^2; A25 := A*A24; A26 := A13^2; A27 := A*A26;
  A28 := A14^2; A29 := A*A28; A30 := A15^2; A31 := A*A30;
  A34A2A1 := (A3 + 4*A2 + A - 1); A34A2A1sq := A34A2A1^2; AB := A*B;
  den := A8*A34A2A1*A34A2A1sq;
  radden := (B+1)^3;
  inv := 1/(radden*den);
  denomnewB := radden*inv;
  denomnewA := A34A2A1sq*denomnewB;
  C :=  (A3*B*(AB-1)^5*(B+1-AB)^3*inv*den)^tredecim_exp;
  newA := denomnewA*((((((((((((((-A21 - 2*A20 + 2*A19 - A18 - 18*A17 + A16 + 25*A15 - 43*A14 - 41*A13 + 77*A12 - 10*A11 - 108*A10 + 63*A9 + 61*A8 - 87*A7 - 2*A6 + 49*A5 - 18*A4 - 11*A3 + 7*A2 + A - 1)*B - A24 - 3*A23 -
    22*A20 - 17*A19 + 27*A18 - 36*A17 - 99*A16 + 60*A15 + 49*A14 - 187*A13 - 9*A12 + 169*A11 - 118*A10 - 104*A9 + 125*A8 + A7 - 66*A6 + 23*A5 + 13*A4 - 8*A3 - A2 + A)*C + ((A19 + 2*A18 - 
    A17 + 2*A16 + 14*A15 + A14 - 10*A13 + 28*A12 + 19*A11 - 29*A10 + 14*A9 + 32*A8 - 21*A7 - 5*A6 + 15*A5 - 4*A4 - 2*A3 + A2)*B + (A22 + 3*A21 + A20 + 2*A19 + 19*A18 + 16*A17 - 8*A16 +
    33*A15 + 60*A14 - 18*A13 + 2*A12 + 82*A11 - 32*A9 + 41*A8 + 11*A7 - 17*A6 + 6*A5 + 2*A4 - A3)))*C + ((-A20 - 3*A19 - A18 - A17 - 16*A16 - 15*A15 + 9*A14 - 18*A13 - 47*A12 + 10*A11 +
    15*A10 - 46*A9 - 11*A8 + 26*A7 - 10*A6 - 11*A5 + 6*A4 + A3 - A2)*B - A23 - 4*A22 - 4*A21 - 3*A20 - 21*A19 - 35*A18 - 8*A17 - 25*A16 - 93*A15 - 42*A14 + 16*A13 - 84*A12 - 82*A11 +
    32*A10 - 9*A9 - 52*A8 + 6*A7 + 11*A6 - 8*A5 - A4 + A3))*C + ((-A19 - 3*A18 + 2*A16 - 14*A15 - 13*A14 + 20*A13 - 5*A12 - 44*A11 + 17*A10 + 32*A9 - 35*A8 - 12*A7 + 24*A6 - 2*A5 - 7*A4 
    + A3 + A2)*B - A22 - 4*A21 - 3*A20 + A19 - 16*A18 - 30*A17 + 9*A16 + 4*A15 - 73*A14 - 20*A13 + 61*A12 - 42*A11 - 63*A10 + 46*A9 + 16*A8 - 32*A7 + 2*A6 + 8*A5 - A4 - A3))*C + ((-A17 - 
    2*A16 - 2*A14 - 9*A13 - 3*A12 + 2*A11 - 10*A10 - 7*A9 + 4*A8 - 2*A7 - 3*A6 + A5)*B - A20 - 3*A19 - 2*A18 - 3*A17 - 14*A16 - 14*A15 - 3*A14 - 18*A13 - 27*A12 - 4*A11 - 5*A10 - 16*A9 -
    3*A8 + A7 - 2*A6))*C + ((-2*A16 - 2*A15 + 4*A14 - 4*A13 - 14*A12 + 10*A11 + 8*A10 - 22*A9 + 2*A8 + 14*A7 - 8*A6 - 2*A5 + 2*A4)*B - 2*A19 - 4*A18 + 2*A17 - 2*A16 - 22*A15 - 2*A14 +
    18*A13 - 30*A12 - 22*A11 + 30*A10 - 6*A9 - 20*A8 + 10*A7 + 2*A6 - 2*A5))*C + ((2*A14 + 2*A13 - 2*A12 + 4*A11 + 8*A10 - 4*A9 + 6*A7 - 2*A6)*B + (2*A17 + 4*A16 + 4*A14 + 16*A13 + 4*A12 -
    2*A11 + 16*A10 + 6*A9 - 4*A8 + 4*A7)))*C + ((A14 + A13 - 2*A12 + A11 + 5*A10 - 3*A9 - 3*A8 + 4*A7 - A5)*B + (A17 + 2*A16 - A15 + 8*A13 + A12 - 7*A11 + 6*A10 + 5*A9 - 5*A8 + A6)))*C 
    + ((A13 + 2*A12 + A11 + A10 + 3*A9 + 2*A8)*B + (A16 + 3*A15 + 3*A14 + 3*A13 + 7*A12 + 8*A11 + 4*A10 + 3*A9 + 3*A8 + A7)))*C + ((-A10 - A9 + A8 - A6)*B - A13 - 2*A12 - 3*A9 - A8 +
    A7))*C + ((A10 - A8 + A7)*B + (A13 + A12 - A11 + A10 + 2*A9 - A8)))*C + (-A8*B - A11 - A10 - A8))*C + -A11 - 4*A10 - 2*A9);
  newB := denomnewB*((((((((((((((10*A28 + 28*A27 - 8*A25 + 14*A24 - 420*A23 - 800*A22 - 398*A21 - 2062*A20 - 4814*A19 - 2468*A18 - 2288*A17 - 9560*A16 - 7898*A15 - 286*A14 - 4982*A13 - 8934*A12 - 2178*A11 + 1142*A10 -
    1330*A9 - 2316*A8 - 412*A7 + 996*A6 + 160*A5 - 376*A4 - 94*A3 + 64*A2 + 28*A + 2)*B + (10*A31 + 38*A30 + 28*A29 + 2*A28 + 44*A27 - 378*A26 - 1228*A25 - 1202*A24 - 2894*A23 - 8096*A22 -
    8462*A21 - 7192*A20 - 18286*A19 - 23976*A18 - 12576*A17 - 15534*A16 - 27720*A15 - 17532*A14 - 5560*A13 - 9362*A12 - 10396*A11 - 3932*A10 + 658*A9 - 132*A8 - 1558*A7 - 362*A6 + 406*A5 +
    120*A4 - 62*A3 - 28*A2 - 2*A))*C + ((A27 - 10*A26 - 44*A25 - 50*A24 - 23*A23 + 15*A22 + 106*A21 + 14*A20 + 361*A19 + 1870*A18 + 1512*A17 - 176*A16 + 3079*A15 + 5236*A14 + 89*A13 -
    225*A12 + 4349*A11 + 2082*A10 - 1220*A9 - 24*A8 + 881*A7 + 300*A6 - 228*A5 - 136*A4 + 32*A3 + 34*A2 + 5*A)*B + (A30 - 9*A29 - 54*A28 - 93*A27 - 82*A26 - 62*A25 + 27*A24 + 46*A23 + 377*A22
    + 2396*A21 + 3553*A20 + 1725*A19 + 5064*A18 + 11507*A17 + 6614*A16 + 2491*A15 + 10858*A14 + 10434*A13 + 1087*A12 + 1624*A11 + 4438*A10 + 1779*A9 - 364*A8 - 239*A7 + 276*A6 + 168*A5 - 27*A4 
    - 34*A3 - 5*A2)))*C + ((-A26 + 11*A25 + 74*A24 + 123*A23 + 96*A22 + 306*A21 + 609*A20 + 316*A19 + 358*A18 + 939*A17 + 95*A16 - 344*A15 + 696*A14 - 461*A13 - 1393*A12 + 244*A11 + 32*A10 -
    931*A9 - 193*A8 + 202*A7 - 3*A6 - 80*A5 - 10*A4 + 11*A3 + 3*A2)*B - A29 + 10*A28 + 85*A27 + 196*A26 + 229*A25 + 487*A24 + 1112*A23 + 1145*A22 + 1065*A21 + 2138*A20 + 1835*A19 + 339*A18 + 
    1429*A17 + 846*A16 - 2270*A15 - 923*A14 + 129*A13 - 2517*A12 - 1876*A11 + 36*A10 - 394*A9 - 555*A8 - 120*A7 + 68*A6 + 12*A5 - 11*A4 - 3*A3))*C + ((-A25 + 9*A24 + 12*A23 - 102*A22 -
    214*A21 - 108*A20 - 358*A19 - 968*A18 - 759*A17 - 631*A16 - 1282*A15 - 861*A14 - 436*A13 - 905*A12 - 183*A11 + 391*A10 - 212*A9 - 242*A8 + 122*A7 + 149*A6 - 12*A5 - 41*A4 - 10*A3 - A2)*B 
    - A28 + 8*A27 + 21*A26 - 91*A25 - 308*A24 - 301*A23 - 556*A22 - 1641*A21 - 2058*A20 - 1868*A19 - 3138*A18 - 3648*A17 - 2557*A16 - 2995*A15 - 2587*A14 - 589*A13 - 803*A12 - 1050*A11 +
    181*A10 + 447*A9 - 22*A8 - 144*A7 + 10*A6 + 40*A5 + 10*A4 + A3))*C + ((7*A23 + 16*A22 + 47*A21 + 208*A20 + 394*A19 + 408*A18 + 639*A17 + 1143*A16 + 1266*A15 + 1049*A14 + 753*A13 +
    775*A12 + 1066*A11 + 381*A10 - 383*A9 + 23*A8 + 283*A7 + 42*A6 - 73*A5 - 33*A4 - 5*A3)*B + (7*A26 + 23*A25 + 63*A24 + 262*A23 + 625*A22 + 865*A21 + 1302*A20 + 2377*A19 + 3195*A18 +
    3315*A17 + 3383*A16 + 3566*A15 + 3804*A14 + 2849*A13 + 910*A12 + 766*A11 + 1210*A10 + 286*A9 - 283*A8 - 72*A7 + 67*A6 + 33*A5 + 5*A4)))*C + ((-3*A22 - 10*A21 - 17*A20 - 128*A19 - 371*A18 
    - 384*A17 - 364*A16 - 947*A15 - 1237*A14 - 698*A13 - 550*A12 - 702*A11 - 536*A10 - 262*A9 + 50*A8 + 96*A7 - 34*A6 - 52*A5 - 11*A4)*B - 3*A25 - 13*A24 - 27*A23 - 148*A22 - 512*A21 -
    782*A20 - 893*A19 - 1807*A18 - 2929*A17 - 2666*A16 - 2434*A15 - 3078*A14 - 2813*A13 - 1817*A12 - 987*A11 - 451*A10 - 374*A9 - 225*A8 + 12*A7 + 52*A6 + 11*A5))*C + ((-3*A21 + 10*A20 +
    43*A19 + 30*A18 + 132*A17 + 432*A16 + 379*A15 + 242*A14 + 747*A13 + 854*A12 + 266*A11 + 156*A10 + 283*A9 + 151*A8 - 7*A7 - 29*A6 - 6*A5 - A4)*B - 3*A24 + 7*A23 + 53*A22 + 70*A21 +
    169*A20 + 617*A19 + 884*A18 + 786*A17 + 1543*A16 + 2369*A15 + 1708*A14 + 1286*A13 + 1664*A12 + 1238*A11 + 455*A10 + 141*A9 + 85*A8 + 38*A7 + 6*A6 + A5))*C + ((-A20 + 8*A19 + 3*A18 -
    30*A17 - 13*A16 - 87*A15 - 296*A14 - 243*A13 - 162*A12 - 343*A11 - 309*A10 - 124*A9 - 22*A8 + 20*A7 + 10*A6 + A5)*B - A23 + 7*A22 + 11*A21 - 28*A20 - 36*A19 - 89*A18 - 410*A17 - 581*A16 
    - 513*A15 - 891*A14 - 1162*A13 - 818*A12 - 552*A11 - 393*A10 - 202*A9 - 78*A8 - 15*A7 - A6))*C + ((-3*A18 - 19*A17 - 24*A16 - 51*A15 - 72*A14 + 95*A13 + 185*A12 + 7*A11 + 7*A10 + 128*A9 
    + 103*A8 + 40*A7 + 9*A6)*B - 3*A21 - 22*A20 - 43*A19 - 78*A18 - 145*A17 - 20*A16 + 205*A15 + 72*A14 + 56*A13 + 439*A12 + 471*A11 + 207*A10 + 49*A9 - 10*A8 - 7*A7))*C + ((-7*A17 + 4*A16 +
    59*A15 + 87*A14 + 104*A13 + 57*A12 - 80*A11 - 41*A10 + 61*A9 + 49*A8 + 17*A7 + A6)*B - 7*A20 - 3*A19 + 63*A18 + 139*A17 + 188*A16 + 224*A15 + 123*A14 + 77*A13 + 177*A12 + 28*A11 -
    159*A10 - 113*A9 - 31*A8 - A7))*C + ((-4*A16 + 3*A15 - 33*A14 - 129*A13 - 148*A12 - 108*A11 - 2*A10 + 64*A9 + 21*A8 + 2*A7)*B - 4*A19 - A18 - 30*A17 - 166*A16 - 278*A15 - 286*A14 -
    272*A13 - 201*A12 - 141*A11 - 74*A10 - 4*A9 + A8))*C + ((4*A14 + 5*A13 + 74*A12 + 116*A11 + 47*A10 + 3*A9)*B + (4*A17 + 9*A16 + 80*A15 + 232*A14 + 321*A13 + 334*A12 + 228*A11 + 66*A10 + 
    7*A9)))*C + (-6*A14 - 63*A13 - 182*A12 - 229*A11 - 120*A10 - 18*A9 - A8)*B - 15*A16 - 46*A15 - 63*A14 - 120*A13 - 184*A12 - 161*A11 - 75*A10 - 10*A9);
  return newA, newB;  
end function;


function act_with_two_on_Montgomery_min(A, exp)

  /*
   Given a Montgomery^- coefficient A, returns a new Montgomery^- coefficient
   obtained from performing a horizontal 2^exp-isogeny. The sign of exp indicates
   the direction of the isogeny.
   Note that this function is not used in our implementation since we work
   with the faster 4-isogenies instead.
  */

  if exp eq 0 then 
    return A;
  else
  A *:= Sign(exp);
  delta := (A^2 + 4)^sq_exp;
    A := 2*(A-3*delta)/(A+delta);
  end if;
  for i in [2..Abs(exp)] do
    eps := (A^2 - 4)^sq_exp;
    A := 2*(3 - A*(A - eps));
  end for;
  eps := (A^2 - 4)^sq_exp;
  scalefac := (eps*(eps + A)/2)^sq_exp;
  return Sign(exp)*(-A-3*eps)/(2*scalefac);
end function;


function act_with_three_on_Montgomery(A, exp)

  /*
   Given a Montgomery coefficient A, returns a new Montgomery coefficent
   obtained from performing a horizontal 3^exp-isogeny. The sign of exp indicates
   the direction of the isogeny. We implicitly assume that we work on the floor,
   since otherwise calling Weier_to_Montgomery would give incorrect results.
   Note that this function is not used in our implementation since we work with
   the faster 9-isogenies instead.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    xP := sample_ell_torsion_point_Montgomery(A, 3);
    M, N := Montgomery_to_Tate(A, xP, sq_exp : ell_eq_three := true);
    M *:= -1;
    for i := 1 to Abs(exp) do
      M, N := three_iso(M, N);
    end for;
    M *:= -1;
    A := Weier_to_Montgomery([M,0,N,0,0]);
  end if;
  return A*Sign(exp);
end function;


function act_with_four_on_Montgomery_min(A, exp)

  /*
   Given a Montgomery^- coefficient A, this function returns a new Montgomery^-
   coefficent obtained from performing a horizontal 4^exp-isogeny. The sign of
   exp indicates the direction of the isogeny.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    d := (A^2 + 4)^sq_exp;
    D := ((A-d)^2+4)^sq_exp;
    r := (D+d-A)/2;;
    t := (((r+A)*r-1)*r)^sq_exp;
    _, A := Montgomery_min_to_Tate_four(A,r,t);
    for i := 1 to Abs(exp) do
      A := four_iso(A);
    end for;
  end if;
  return Sign(exp)*Tate_four_to_Montgomery_min(A);
end function;


function act_with_five_on_Montgomery(A, exp)

  /*
   Given a Montgomery coefficient A, returns a new Montgomery coefficent
   obtained from performing a horizontal 5^exp-isogeny. The sign of exp indicates
   the direction of the isogeny. We implicitly assume that we work on the floor,
   since otherwise calling Weier_to_Montgomery would give incorrect results.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    xP := sample_ell_torsion_point_Montgomery(A, 5);
    _, A := Montgomery_to_Tate(A, xP);
    A := -A;
    for i := 1 to Abs(exp)-1 do
      A := five_iso(A);
    end for;
    A := -A;
    A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4;
    a1 := A+1; a2 := A; a3 := a2;
    a4 := 5*A3-10*A2-5*A;
    a6 := A5-10*A4-5*A3-15*A2-A;
    A := Weier_to_Montgomery([a1,a2,a3,a4,a6]);
  end if;
  return A*Sign(exp);
end function;


function act_with_seven_on_Montgomery(A, exp)

  /*
   Given a Montgomery coefficient A, returns a new Montgomery coefficent
   obtained from performing a horizontal 7^exp-isogeny. The sign of exp indicates
   the direction of the isogeny. We implicitly assume that we work on the floor,
   since otherwise calling Weier_to_Montgomery would give incorrect results.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    xP := sample_ell_torsion_point_Montgomery(A, 7);
    M, N := Montgomery_to_Tate(A, xP);
    A := N/(M-1);
    for i := 1 to Abs(exp)-1 do
      A := seven_iso(A);
    end for;
    A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
    A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
    a1 := 1+A-A2; a2 := A2-A3; a3 := a2;
    a4 := (-5*A7 + 35*A5 - 70*A4 + 70*A3 - 35*A2 + 5*A);
    a6 := (-A11 - 8*A10 + 46*A9 - 107*A8 + 202*A7 - 343*A6 + 393*A5 - 258*A4 + 94*A3 - 19*A2 + A);
    A := Weier_to_Montgomery([a1,a2,a3,a4,a6]);
  end if;
  return A*Sign(exp);
end function;


function act_with_nine_on_Montgomery(A, exp)

  /*
   Given a Montgomery coefficient A, returns a new Montgomery coefficent
   obtained from performing a horizontal 9^exp-isogeny. The sign of exp indicates
   the direction of the isogeny. We implicitly assume that we work on the floor,
   since otherwise calling Weier_to_Montgomery would give incorrect results.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    xP := sample_ell_torsion_point_Montgomery(A, 9);
    M, N := Montgomery_to_Tate(A, xP);
    A := (M-1)^2/(M - N - 1);
    for i := 1 to Abs(exp)-1 do
      A := nine_iso(A);
    end for;
    A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
    A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
    A12 := A6^2; A13 := A*A12; A14 := A7^2; A15 := A*A14; A16 := A8^2;
    A17 := A*A16;
    a1 := -A3+A2+1; a2 := -A5+2*A4-2*A3+A2; a3 := a2;
    a4 := (-5*A11 + 5*A10 + 40*A9 - 165*A8 + 360*A7 - 540*A6 + 570*A5 - 405*A4 + 185*A3 - 50*A2 + 5*A);
    a6 := (-A17 - 7*A16 + 63*A15 - 230*A14 + 641*A13 - 1639*A12 +
    	   3691*A11 - 6707*A10 + 9425*A9 - 10174*A8 + 8456*A7 - 5379*A6 +
    	   2559*A5 - 865*A4 + 190*A3 - 24*A2 + A);
    A := Weier_to_Montgomery([a1,a2,a3,a4,a6]);
  end if;
  return A*Sign(exp);
end function;


function act_with_eleven_on_Montgomery(A, exp)

  /*
   Given a Montgomery coefficient A, returns a new Montgomery coefficent
   obtained from performing a horizontal 11^exp-isogeny. The sign of exp indicates
   the direction of the isogeny. We implicitly assume that we work on the floor,
   since otherwise calling Weier_to_Montgomery would give incorrect results.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    xP := sample_ell_torsion_point_Montgomery(A, 11);
    M, N := Montgomery_to_Tate(A, xP);
    M2 := M^2; M3 := M*M2; MN := M*N; N2 := N^2;
    denomA := (M - N - 1);
    denomB := (M3 - 4*M2 + MN + 5*M - N - 2);
    invAB := 1/(denomA*denomB);
    invA := invAB*denomB; invB := invAB*denomA;
    A := (-M2 + 3*M - N - 2)*invA;
    B := (M2 - 2*MN - 2*M + N2 + 2*N + 1)*invB;
    for i := 1 to Abs(exp)-1 do
      A, B := eleven_iso(A, B);
    end for;
    A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
    A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
    A12 := A6^2; A13 := A*A12; A14 := A7^2; A15 := A*A14; A16 := A8^2;
    A17 := A*A16; A18 := A9^2; A19 := A*A18; A20 := A10^2; A21 := A*A20;
    a1 :=  ((A2 - A)*B + 1);
    a2 := ((-A5 + A4 - A3 + 2*A2 - A)*B - A4 + A3); a3 := a2;
    a4 := ((-5*A13 + 30*A12 - 45*A11 + 135*A10 - 185*A9 + 295*A8 -
           325*A7 + 215*A6 - 235*A5 + 145*A4 - 30*A2 + 10*A)*B - 5*A12 + 30*A11
           - 40*A10 + 100*A9 - 115*A8 + 160*A7 - 145*A6 + 5*A5 - 25*A4 + 70*A3
           - 35*A2 + 5*A);
    a6 := ((-A21 + 18*A20 - 66*A19 + 211*A18 - 451*A17 +
            1173*A16 - 1839*A15 + 2959*A14 - 4582*A13 + 4982*A12 - 5273*A11 +
            5351*A10 - 3937*A9 + 2133*A8 - 1217*A7 + 868*A6 - 318*A5 - 58*A4 +
            53*A3 - 7*A2 + 2*A)*B - A20 + 18*A19 - 65*A18 + 192*A17 - 368*A16 +
            917*A15 - 1298*A14 + 1756*A13 - 2603*A12 + 2368*A11 - 1800*A10 +
            1703*A9 - 1157*A8 + 190*A7 + 170*A6 + 183*A5 - 322*A4 + 138*A3 -
            21*A2 + A);
    A := Weier_to_Montgomery([a1,a2,a3,a4,a6]);
  end if;
  return A*Sign(exp);
end function;


function act_with_thirteen_on_Montgomery(A, exp)

  /*
   Given a Montgomery coefficient, returns a new Montgomery coefficent
   obtained from performing a horizontal 11^exp-isogeny. The sign of exp indicates
   the direction of the isogeny. We implicitly assume that we work on the floor,
   since otherwise calling Weier_to_Montgomery would give incorrect results.
  */

  if exp eq 0 then
    return A;
  else
    A *:= Sign(exp);
    xP := sample_ell_torsion_point_Montgomery(A, 13);
    M, N := Montgomery_to_Tate(A, xP);
    M2 := M^2; M3 := M*M2; MN := M*N; N2 := N^2;
    denomB := (M3 - 4*M2 + MN + 5*M - N - 2);
    denomA := (M3 - 3*M2 - MN + 3*M +  N2 + N - 1);
    invAB := 1/(denomA*denomB);
    invB := invAB*denomA; invA := invAB*denomB;
    B := (-M3 + 3*M2 + MN - 3*M - N2 - N + 1)*invB;
    A := (-M3 + M2*N + 4*M2 - 4*MN - 5*M + N2 + 3*N + 2)*invA;

    for i := 1 to Abs(exp)-1 do
      A, B := thirteen_iso(A, B);
    end for;
    A2 := A^2; A3 := A*A2; A4 := A2^2; A5 := A*A4; A6 := A3^2;
    A7 := A*A6; A8 := A4^2; A9 := A*A8; A10 := A5^2; A11 := A*A10;
    A12 := A6^2; A13 := A*A12; A14 := A7^2; A15 := A*A14; A16 := A8^2;
    A17 := A*A16; A18 := A9^2; A19 := A*A18; A20 := A10^2; A21 := A*A20;
    A22 := A11^2; A23 := A*A22; A24 := A12^2; A25 := A*A24; A26 := A13^2;
    A27 := A*A26; A28 := A14^2; A29 := A*A28; A30 := A15^2; A31 := A*A30;
    A32 := A16^2; A33 := A*A32; A34 := A17^2; A35 := A*A34; A36 := A18^2;
    A37 := A*A36; Ap12 := (A+1)^2; Ap13 := (A+1)*Ap12; Ap14 := Ap12^2;
    inv11 := 1/(A+1)^11; inv10 := inv11*(A+1); inv7 := inv10*Ap13;
    inv6 := inv7*(A+1); inv2 := inv6*Ap14; inv1 := inv2*(A+1);
    a1 :=  ((-A4 - A3 + A2)*inv2*B + (A2 + A + 1)*inv1);
    a2 := ((-A7 - A6 + A5 - A4 - 2*A3 + A2)*inv1*B + (A5
            - A3 + A2)); a3 := a2;
    a4 := ((-5*A23 - 20*A22 + 45*A21 + 450*A20 +
           1385*A19 + 3110*A18 + 6820*A17 + 13450*A16 + 21265*A15 + 28660*A14 +
           37250*A13 + 46210*A12 + 49410*A11 + 44150*A10 + 35515*A9 + 28080*A8 +
           20330*A7 + 11120*A6 + 3910*A5 + 780*A4 + 60*A3)*inv7*B + (5*A21 + 15*A20 - 60*A19 -
           395*A18 - 1010*A17 - 2055*A16 - 4310*A15 - 7730*A14 - 10455*A13 -
           11900*A12 - 13710*A11 - 15345*A10 - 13715*A9 - 8665*A8 - 4160*A7 -
           2600*A6 - 2170*A5 - 1265*A4 - 430*A3 - 75*A2 - 5*A)*inv6);
    a6 := ((-A37 + 2*A36 + 107*A35 +
           730*A34 + 2767*A33 + 8554*A32 + 27743*A31 + 88851*A30 + 245155*A29 +
           573114*A28 + 1186101*A27 + 2251384*A26 + 3954034*A25 + 6417918*A24 +
           9638501*A23 + 13440992*A22 + 17512516*A21 + 21450071*A20 + 24642172*A19
           + 26303325*A18 + 26041720*A17 + 24157546*A16 + 21052162*A15 +
           16919262*A14 + 12295396*A13 + 8121927*A12 + 4985463*A11 + 2834443*A10 +
           1419204*A9 + 581761*A8 + 181949*A7 + 40527*A6 + 5877*A5 + 473*A4 +
           13*A3)*inv11*B + (A35 - 3*A34 - 104*A33 -
           627*A32 - 2138*A31 - 6309*A30 - 20703*A29 - 65382*A28 - 171329*A27 -
           374877*A26 - 725767*A25 - 1291042*A24 - 2122987*A23 - 3214262*A22 -
           4470147*A21 - 5720340*A20 - 6805336*A19 - 7608523*A18 - 7924950*A17 -
           7513576*A16 - 6460888*A15 - 5182862*A14 - 3932961*A13 - 2693744*A12 -
           1550887*A11 - 736429*A10 - 321311*A9 - 157770*A8 - 84493*A7 - 38601*A6
           - 12876*A5 - 2913*A4 - 417*A3 - 33*A2 - A)*inv10);
    A := Weier_to_Montgomery([a1,a2,a3,a4,a6]);
  end if;
  return A*Sign(exp);
end function;


function csidh_action_old(private_key, A)

  /*
   This is the implementation by Bernstein et al to compute the CSIDH class group action.
   The degree bound parameter input was removed and we work with a bound of 113 as mentioned
   at the top of this file. The reason for this is that this is the cut-off point
   where the new method starts to outperform the old method. This implies for ell starting 
   from 113 we swap to the O(sqrt(ell)) complexity formulas instead of the O(ell) Vélu-formulas
   by Renes in the original CSIDH.
   Note that the input A represents a Montgomery coefficient, unlike csidh_action_new, which
   requires a Montgomery^- coefficient.
  */

  A := F ! A;
  while private_key ne [0 : i in [1..#private_key]] do
    xP := Random(F);
    twist := not IsSquare(((xP+A)*xP+1)*xP); if twist then A := -A; xP := -xP; end if;
    indices_ells_correct_sign := [];
    k := 1;
    for i := 1 to #ells do
      if private_key[#ells-i+1] gt 0 and not twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
    elif private_key[#ells-i+1] lt 0 and twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
      end if;
    end for;
    XQ, ZQ := scalar_multiplication_Montgomery((p+1) div k, xP, 1, A);
    for i in indices_ells_correct_sign do
      if ZQ ne 0 then
        xQ := XQ/ZQ;
        ell := ells[i];
        XR, ZR := scalar_multiplication_Montgomery(k div ell, xQ, 1, A);
        if ZR ne 0 then
          A, XQ, ZQ := act_with_ell_on_Montgomery(A, ell, XR/ZR, xQ,degree_bound);
          if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
        end if;
      end if;
    end for;
    if twist then A := -A; end if;
  end while;
  return A;
end function;



function csidh_action_new(private_key, A)

  /*
   This function calculates the CSIDH class group action. We first use radical isogenies
   to compute the chains of 2-, 3-, 5-, 7-, 11- and 13-isogenies. After that, we swap to
   the formulas from the original CSIDH and those from Bernstein et al to compute the rest
   of the isogenies.
   Remark that we start from a Montgomery^- coefficient, compute the 2^k-isogeny first,
   then swap to Montgomery coefficients to compute the rest of the isogenies, and at
   the end we go back to a Montgomery^- coefficient. The swaps between Montgomery and
   Montgomery^- coefficients are vertical isogenies with kernel <(0,0)>. The reason is that
   in the setting where 2-isogenies are being used, a Montgomery^- coefficient is easier for
   key validation since all of these live on the surface, whereas Montgomery coefficients can
   live on both the floor and the surface. Additionially, going from Montgomery^- on the floor
   to Tate normal form is easier due to having to solve a cubic with only one rational root.
  */

  A := F ! A;
  A := act_with_four_on_Montgomery_min(A, private_key[1] div 2);
  A := Montgomery_min_to_Montgomery(A);
  if IsOdd(private_key[1]) then A := 2-(4*((2+A)^sq_exp-2)^4)/(2-A)^2; end if;
  private_key := Remove(private_key, 1);
  A := act_with_nine_on_Montgomery(A, private_key[1] div 2);
  private_key[1] := private_key[1] mod 2;
  if Abs(private_key[2]) gt 1 then
    A := act_with_five_on_Montgomery(A, private_key[2]);
    private_key[2] := 0;
  end if;
  if Abs(private_key[3]) gt 1 then
    A := act_with_seven_on_Montgomery(A, private_key[3]);
    private_key[3] := 0;
  end if;
  if Abs(private_key[4]) gt 1 then
    A := act_with_eleven_on_Montgomery(A, private_key[4]);
    private_key[4] := 0;
  end if;
  if Abs(private_key[5]) gt 1 then
    A := act_with_thirteen_on_Montgomery(A, private_key[5]);
    private_key[5] := 0;
  end if;
  
  while private_key ne [0 : i in [1..#private_key]] do
    xP := Random(F);
    twist := not IsSquare(((xP+A)*xP+1)*xP); if twist then A := -A; xP := -xP; end if;
    indices_ells_correct_sign := [];
    k := 1;
    for i := 1 to #ells do
      if private_key[#ells-i+1] gt 0 and not twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
    elif private_key[#ells-i+1] lt 0 and twist then Append(~indices_ells_correct_sign,#ells-i+1); k *:= ells[#ells-i+1];
      end if;
    end for;
    XQ, ZQ := scalar_multiplication_Montgomery((p+1) div k, xP, 1, A);
    for i in indices_ells_correct_sign do
      if ZQ ne 0 then
        xQ := XQ/ZQ;
        ell := ells[i];
        XR, ZR := scalar_multiplication_Montgomery(k div ell, xQ, 1, A);
        if ZR ne 0 then
          A, XQ, ZQ := act_with_ell_on_Montgomery(A, ell, XR/ZR, xQ,degree_bound);
          if twist then private_key[i] +:= 1; else private_key[i] -:= 1; end if;
        end if;
      end if;
    end for;
    if twist then A := -A; end if;
  end while;
  A := Montgomery_to_Montgomery_min(A);
  return A;
end function;


function csidh_private_keygen()

  /*
   The original CSIDH private key had all exponents sampled from an interval [-5..5].
  */

  return [Random([-5..5]) : i in [1..74]];
end function;


function cradical_private_keygen()

  /*
   This is the (skew) interval from which private keys should be sampled in case radical
   isogenies are used as well. The interval was obtained empirically but is (near) optimal.
  */

  return [Random([-202..202]), Random([-170..170]), Random([-95..95]),
         Random([-91..91]), Random([-33..33]), Random([-29..29])] cat
         [Random([-6..6]) : i in [1..20]] cat [Random([-5..5]) : i in [1..14]] cat
         [Random([-4..4]) : i in [1..10]] cat [Random([-3..3]) : i in [1..10]] cat
         [Random([-2..2]) : i in [1..8]] cat [Random([-1..1]) : i in [1..7]];
end function;


procedure csidh_key_exchange_new()
  t := Cputime();
  alice_private := cradical_private_keygen();
  bob_private := cradical_private_keygen();
  alice_public := csidh_action_new(alice_private,0);
  printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_new(bob_private,0);
  printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_new(alice_private, bob_public);
  bob_alice := csidh_action_new(bob_private, alice_public);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the new version.";
  else
    printf "new time : %o\n", Cputime(t);
    printf "The joint key is %o.\n", alice_bob;
  end if;
end procedure;


procedure csidh_key_exchange_old()
  t := Cputime();
  alice_private := csidh_private_keygen();
  bob_private := csidh_private_keygen();
  alice_public := csidh_action_old(alice_private,0);
  printf "Alice's public key is %o.\n", alice_public;
  bob_public := csidh_action_old(bob_private,0);
  printf "Bob's public key is %o.\n", bob_public;
  alice_bob := csidh_action_old(alice_private, bob_public);
  bob_alice := csidh_action_old(bob_private, alice_public);
  if alice_bob ne bob_alice then
    print "Error! The computations of the joint key do not match in the new version.";
  else
    printf "new time : %o\n", Cputime(t);
    printf "The joint key is %o.\n", alice_bob;
  end if;
end procedure;



csidh_key_exchange_new();


