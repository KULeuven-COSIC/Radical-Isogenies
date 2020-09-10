# Radical-Isogenies

The files contained in this repository are the Magma codes associated with the paper
'Radical Isogenies' by Wouter Castryck, Thomas Decru & Frederik Vercauteren.



The file radical_formulas.m contains the formulas for radical N-isogenies for N = 2,
..., 13. More precisely, let E be an elliptic curve in a general form such that P =
(0,0) is an N-torsion point. Formulas are given for:
- the Tate-Pairing t of (P,-P) in function of the coefficients of E;
- an N-torsion point PA on EA = E/&lt;P&gt; defined over a field that is obtained
  by adjoining an N-th root of t; furthermore, PA is the canonical N-torsion
  point such that dual isogeny of E -> E/&lt;P&gt; maps PA to the point Q such that N*Q=P;
- an isomorpic form Eiso of EA such that PA is translated to (0,0) and Eiso has
  the same form as E.

For N = 2 we use the Montgomery form of an elliptic curve.
For N = 3 we use a Weierstrass form that is isomorphic to a Hessian form.
For N > 3 we use the Tate normal form of an elliptic curve.
From N = 6 onwards, we use the optimized equations by Sutherland that can be found here:
http://math.mit.edu/~drew/X1_optcurves.html



The file crad_512.m contains a Magma implementation for the CSIDH key exchange protocol,
which was built upon the code of Bernstein, De Feo, Leroux and Smith and can be found
here: https://velusqrt.isogeny.org/software.html

The main adjustments to the code correspond to implementing radical N-isogenies to
speed up the CSIDH protocol. The 2-isogenies are implemented by using radical
4-isogenies, and - likewise - the 3-isogenies are calculated by means of 9-isogenies.
Apart from that, radical 5-, 7-, 11- and 13-isogenies are also implemented. The sampling
box for the exponents is changed, and is now very skewed towards computing a lot more
isogenies of the smallest degree. Both the old and new way of computing the class group
action can be used to perform a key exhcange, with the procedures csidh_key_exchange_old(),
resp. csidh_key_exchange_new().
