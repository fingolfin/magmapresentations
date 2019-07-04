//$Id:: sl2q.m 2340 2012-09-30 01:03:09Z eobr007                             $:

// Campbell, Robertson, Williams J. Austral. Math. Soc. 1990 
// Campbell and Robertson, BLMS 1980 

/* generators for SL(2, p^e) */

SL2Generators := function (p, e)

  F := GF (p, e);
  w := PrimitiveElement (F);

  delta := GL(2, F) ![w^-1, 0, 0, w^1];
  tau := GL(2, F) ![1, 1, 0, 1];
  Z := GL(2, F) ![0,1,-1,0];

  if e eq 1 then 
     return [tau, Z];
  else 
    return [delta, tau, Z];
  end if;
end function;

// presentation for SL(2, p^e); p odd 
// Projective = true: return presentation for PSL 

SL2_odd := function (p, e: Projective := false)
   K := GF (p, e);
   q := p^e;
   w := PrimitiveElement (K);
   I := Integers ();

   Q<delta, tau, U> := SLPGroup (3);
   Rels := [];

   E := sub < K | w^2>;
   c := Eltseq (E!w^1);
   c := [I!x: x in c];

   tau1 := &*[(tau^(delta^(i)))^c[i + 1]: i in [0..e - 1]];
   Rels cat:= [ tau^p = 1, (tau, tau1) = 1, (tau1, tau^delta) = 1, 
               (tau1 * U * delta)^3 = 1];

   if Projective then 
      Rels cat:= [(tau * U)^3 = 1, (U * delta)^2 = 1, U^2 = 1, 
                  delta^((q - 1) div 2) = 1];
   else 
      Rels cat:= [(tau * U^-1)^3 = U^2, (U * delta)^2 = U^2, U^4 = 1, 
                  delta^((q - 1) div 2) = U^2];
   end if;

   if IsSquare (1 + w^1) then  
      m := Log (w^2, 1 + w^1);
      Append (~Rels, tau^(delta^m) = tau * tau1);
      Append (~Rels, tau1^(delta^m) = tau1 * tau^delta);
   else 
      m := Log (w^2, (1 + w^-1));
      Append (~Rels, tau1^(delta^m) = tau * tau1);
      Append (~Rels, tau^(delta^(m + 1)) = tau1 * tau^delta);
   end if;

   f := MinimalPolynomial (w^1, GF(p));
   c := Coefficients (f);
   c := [I!x: x in c];
   B := [tau, tau1];
   for i in [2..e] do B[i + 1] := B[i - 1]^delta; end for;
   Append (~Rels, &*[B[i + 1]^c[i + 1]: i in [0..e]]);
   Rels := [LHS (r) * RHS (r)^-1: r in Rels];

   return Q, Rels;
end function;

// special presentation for SL(2, p^e) when p^e mod 4 = 3 

SL2_special := function (p, e: Projective := false)
   K := GF (p, e);
   q := p^e;
   w := PrimitiveElement (K);
   I := Integers ();

   if IsSquare (1 + w^1) then  
      m := Log (w^2, 1 + w^1);
      r := (q + 1) div 4;
   else 
      m := Log (w^2, (1 + w^-1));
      r := (q - 3) div 4;
   end if;

   Q<delta, tau, U> := SLPGroup (3);
   
   Rels := [(tau, tau^(delta^((q + 1) div 4))) = 1,
             tau^(delta^m) = (tau^-1, delta^r)];

   if Projective then 
      Rels cat:= [(tau * U)^3 = 1, (U * delta)^2 = 1, U^2 = 1, 
                  delta^((q - 1) div 2) = tau^p]; 
   else 
      Rels cat:= [(tau * U^-1)^3 = U^2, (U * delta)^2 = U^2, U^4 = 1, 
                  delta^((q - 1) div 2) = tau^p * U^2];
   end if;

   E := sub < K | w^2>;
   c := Eltseq (E!w^1);
   c := [I!x: x in c];

   tau1 := &*[(tau^(delta^(i)))^c[i + 1]: i in [0..e - 1]];

   f := MinimalPolynomial (w^1, GF(p));
   c := Coefficients (f);
   c := [I!x: x in c];
   B := [tau, tau1];
   for i in [2..e] do B[i + 1] := B[i - 1]^delta; end for;
   Append (~Rels, &*[B[i + 1]^c[i + 1]: i in [0..e]]);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels];

   return Q, Rels;
end function;

/* presentation for SL(2, 2^e) where e > 1 */

SL2_even := function (p, e)
   assert p eq 2;
   q := 2^e;

   E := GF (2, e);
   w := PrimitiveElement (E);

   F<delta, tau, U> := SLPGroup (3);
   B := [tau];
   for i in [1..e] do B[i + 1] := B[i]^delta; end for;

   f := MinimalPolynomial (w^2, GF(2));
   c := Coefficients (f);
   I := Integers ();
   u := [I!x: x in c];

   m := Log (w^2, 1 + w^2);
   Rels :=[&*[B[i + 1]^u[i + 1]: i in [0..e]],
        (U * tau)^3, U^2, (U * delta)^2, tau^2, (tau * delta)^(q - 1),
        tau^(delta^m) * (tau, delta)^-1];
   return F, Rels;
end function;

/* Zassenhaus presentation for SL (2, p) where p is not 17 */

Zassenhaus := function (p)
   if p eq 2 then 
      return Group<s, t | s^p = 1, t^2, (s * t)^3>;
   elif p eq 3 then 
      return Group<s, t | s^p = 1, t^4, (t * s^-1 * t^-1 * s^-1 * t * s^-1)>;
   elif p ne 17 then  
      return Group<s, t | s^p = (s * t)^3, (t^2, s), t^4, (s^2 * t * s^((p^2 + 1) div 2) * t)^3>;
   end if;

end function;

// Campbell Robertson presentation for SL(2, p) 

CR := function (p)
   if p eq 2 then 
      return Group<s, t | s^2 = 1, t^2, (s * t)^3>;
   end if;
   k := p div 3;
   F<y, x> := FreeGroup (2);
   G := quo<F| x^2 = (x * y)^3, (x * y^4 * x * y^((p + 1) div 2))^2 * y^p * x^(2 * k)>;
   return G;
end function;

/* Campbell Robertson presentation for SL(2, p) modified for our generators */

Modified_CR := function (p: Projective := false)
   F<a,b> := SLPGroup (2);
   if p eq 2 then 
      return F, [a^2, b^2, (a * b)^3];
   end if;
   r := p mod 3;
   k := p div 3;
   if r eq 1 then 
      Rels := [b^-2 * (b* (a* b^2))^3,
         (b * (a*b^2)^4 * b * (a * b^2)^((p + 1) div 2))^2 * (a * b^2)^p * b^(2*k)];
   else
      Rels := [b^2 * (b^-1* a)^3,
         (b^-1* a^4* b^-1* a^((p + 1) div 2))^2 * a^p * (b^-1)^(2*k)];
   end if;
   if Projective then Rels cat:= [b^2]; end if;
   return F, Rels;
end function;

/* presentation for SL(2, p^e) */

PresentationForSL2 := function (p, e: Projective := false)
   if e eq 1 then 
      Q, R := Modified_CR (p: Projective := Projective);
   elif IsEven (p) then
      Q, R := SL2_even (p, e);
   elif p^e mod 4 eq 3 then 
      Q, R := SL2_special (p, e: Projective := Projective);
   else 
      Q, R := SL2_odd (p, e: Projective := Projective);
   end if;
   return Q, R;
end function;

/* 
SetGlobalTCParameters (:Hard, CosetLimit := 10^8, Print := 10^6);
for p in [2,3,5,7,11,13,17,19,23,29,31] do 
   for e in [1..6] do 
      p, e;
      Q, R := PresentationForSL2 (p, e);
      // ToddCoxeter (Q, sub <Q |>:Hard:=true, Workspace:=10^8);
      X := SL2Generators (p, e);
      Y := Evaluate (R, X);
      assert #Set (Y) eq 1;
      F := SLPToFP (Q, R);
      if e eq 1 then 
      I := CosetImage (F, sub<F| >); 
      else 
      I := CosetImage (F, sub<F| F.1, F.2>);
      end if;
      RandomSchreier (I);
      CompositionFactors (I);
      assert #I in {#SL(2, p^e), #PSL(2, p^e)};
   end for;
end for;

*/
