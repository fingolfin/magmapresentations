import "sl2q.m": PresentationForSL2;
import "signed.m": SignedPermutations;

forward OmegaConvertToStandard, OmegaStandardToPresentation, 
OmegaPresentationToStandard;

OmegaGenerators := function (d, q)
   assert IsOdd (d);
   assert IsOdd (q);
   if d eq 3 then return ClassicalStandardGenerators ("Omega", 3, q); end if;

   n := d div 2;
   assert n gt 1;

   F := GF (q);
   MA := MatrixAlgebra (F, d);
   Z := Identity (MA);
   Z[1,1] := 0; Z[1,2] := 1;
   Z[2,1] := 1; Z[2,2] := 0;
   Z[d,d] := -1;

   w := PrimitiveElement (F);
   Delta := Identity (MA);
   Delta[1,1] := w^-1; 
   Delta[2,2] := w; 
   Delta[3,3] := w^+1;
   Delta[4,4] := w^-1;
   Delta := GL(d, F)!Delta;

   tau := Identity (MA);
   tau[1,1] := 1; tau[1,2] := 1; tau[1,d] := 1;
   tau[d, 2] := 2; tau[d,d] := 1; 

   sigma := Identity (MA);
   sigma[1,1] := 1; sigma[1,3] := 1;
   sigma[4,2] := -1; sigma[4,4] := 1;

   E := ClassicalStandardGenerators ("Omega", d, q);
   U := E[5]; 
   V := E[4];

   gens := [GL(d, q) | Delta, Z, tau, sigma, U, V];
   return gens;
end function;

Omega_PresentationForN1  := function (n)
   assert n gt 1;

   F := SLPGroup (3);
   Z := F.1; U := F.2; V := F.3;
   
   S, R := SignedPermutations (n);
   phi := hom<S-> F | U, V>;
   R := [phi (r): r in R];

   R1 := [];
   if n gt 2 then Append (~R1, (Z, U^V) = 1); end if;
   if n gt 3 then Append (~R1, (Z, V * U^-1) = 1); end if;
   Append (~R1, Z^2 = 1);
   Append (~R1, (Z, U^2) = 1);
   Append (~R1, (Z, Z^U) = 1);
   Rels := [LHS (r) * RHS (r)^-1: r in R1] cat R;
   return F, Rels;
end function;

Omega_OrderN1 := function (n)
   return 2^(2 * n - 1) * Factorial (n);
end function;

Omega_PresentationForN := function (n, q)

   F := SLPGroup (4);
   Delta := F.1; Z := F.2; U := F.3; V := F.4; 

   S, R := Omega_PresentationForN1 (n);
   phi := hom<S->F | Z, U, V>;
   R := [phi (r): r in R];

   R1 := [];
   if n gt 3 then 
     Append (~R1, (Delta, U^(V^2)) = 1); 
     Append (~R1, (Delta, Delta^(V^2)) = 1); 
   end if;
   if n gt 4 then Append (~R1, (Delta, V * U * U^V) = 1); end if;
   if n gt 2 then 
      Append (~R1, (Delta, Z^(V^2)) = 1); 
      Append (~R1, Delta * Delta^V = Delta^(V * U)); 
      Append (~R1, (Delta, Delta^V) = 1);
      Append (~R1, (Delta, (U^2)^V) = 1);
   end if;

   Append (~R1, Delta^U = Delta^-1);
   OMIT := true;
   if not OMIT then 
      Append (~R1, Delta^((q - 1) div 2) = U^2);
   end if;
   Append (~R1, Delta^(Z * Z^U)= Delta^-1);

   if n eq 2 then Append (~R1, (Delta, Delta^Z) = 1); end if;

   Rels := [LHS (r) * RHS (r)^-1: r in R1] cat R;
   return F, Rels;
end function;

Omega_OrderN := function (n, q)
   return (q - 1)^n * 2^(n - 1) * Factorial (n);
end function;

Setup_OmegaPresentation := function (d, q)
   assert IsOdd (d);
   assert IsOdd (q);
   n := d div 2;
   assert n gt 1;
   
   F := GF (q);
   w := PrimitiveElement (F);
   
   f, p, e := IsPrimePower (q);

   F := SLPGroup (6);
   Delta := F.1; Z := F.2; tau := F.3; sigma := F.4; U := F.5; V := F.6;

   R3 := [];

   // additional relation needed for q = p to express Delta as word in sigma and U
   if IsPrime (q) then
      I := Integers ();
      b := I!(1/w);
      w := I!w;
      Append (~R3, Delta = (sigma^U)^(w - w^2) * sigma^(b) * (sigma^U)^((w-1)) * sigma^-1);
   end if;

   if e eq 1 then 
      S, R1 := Omega_PresentationForN1 (n);
      phi := hom<S->F | Z, U, V>;
   else 
      S, R1 := Omega_PresentationForN (n, q);
      phi := hom<S->F | Delta, Z, U, V>;
   end if;
   R1 := [phi (r): r in R1];

   S, R2 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | sigma, U>;
   else 
      phi := hom<S-> F | Delta, sigma, U>;
   end if;
   R2 := [phi (r): r in R2];

   if e gt 1 then 
      Append (~R3, (sigma, Delta^(Z^U)) = 1); 
   end if;

   // centraliser of tau
   R5 := [];
   if n gt 2 then 
      Append (~R5, (tau, U^V) = 1);
      if e gt 1 then Append (~R5, (tau, Delta^V) = 1); end if;
   end if;
   if n gt 3 then Append (~R5, (tau, V * U^-1) = 1); end if;
   Append (~R5, (tau, U^2 * Z^U) = 1);
   if e gt 1 and n eq 2 then Append (~R5, (tau, Delta * Delta^Z) = 1); end if;

   R6 := [];
   S, R6 := PresentationForSL2 (p, e: Projective := true);
   if e eq 1 then 
      phi := hom<S-> F | tau, Z>;
   else 
      x := Delta * Delta^(Z^U);
      phi := hom<S-> F | x, tau, Z>;
   end if;
   R6 := [phi (r): r in R6];

   // Steinberg relations 
   R4 := [];
   if n gt 2 then 
      Append (~R4, (sigma, sigma^V) = sigma^(V * U^-1)); 
      Append (~R4, (sigma, sigma^(V * U^-1)) = 1);
      W := U^(V * U^-1);
      Append (~R4, (sigma, sigma^W) = 1);
      // new relation June 2018
      Append (~R4, (sigma, tau^(V^2)) = 1);
   end if;
   if n gt 3 then 
      Append (~R4, (sigma, sigma^(V^2)) = 1);
   end if;
   Append (~R4, (sigma, sigma^(Z^U)) = 1);
   Append (~R4, (tau, tau^U) = (sigma^(Z^U))^2);
   Append (~R4, (sigma, tau) = 1);
   Append (~R4, (sigma^Z, tau) = sigma * tau^(Z * U));
   
   // Omega(7, 3) has multiplicator of order 6 
   if d eq 7 and q eq 3 then
      Append (~R3, (tau, sigma^V) = 1);
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in R3 cat R4 cat R5] cat R1 cat R2 cat R6; 
   return F, Rels;
end function;

OmegaPresentation := function (d, q: Presentation := false) 
   assert IsOdd (d) and d gt 1;
   assert IsOdd (q);

   if d eq 3 then
      Q, R := ClassicalStandardPresentation ("SL", 2, q: Projective:=true);
      Q := SLPGroup (5);
      R := Evaluate (R, [Q.i: i in [1, 1, 2, 3]]);
      Append (~R, Q.4);
      Append (~R, Q.5);
      return Q, R;
   end if;

   P, R := Setup_OmegaPresentation (d, q);
   if Presentation then return P, R; end if;

   S, Rels := OmegaConvertToStandard (d, q, R);
   Rels := [w : w in Rels | w ne w^0];
   return S, Rels;
end function;

/* relations are on presentation generators;
   convert to relations on standard generators */

OmegaConvertToStandard := function (d, q, Rels)
   A := OmegaStandardToPresentation (d, q);
   Rels := Evaluate (Rels, A);
   B := OmegaPresentationToStandard (d, q);
   C := Evaluate (B, A);
   U := Universe (C);
   W := Universe (Rels);
   tau := hom <U -> W | [W.i:i in [1..Ngens (W)]]>;
   T := [W.i^-1 * tau (C[i]): i in [1..Ngens (W)]];
   Rels cat:= T;
   return W, Rels;
end function;

// word for Delta in Sp(4, 9) generated by 5 specific elements 
SpecialWordForDelta := function()
    G := SLPGroup (5); 
    w10 := G.4 * G.5; w103 := w10 * G.5; w7 := G.3 * G.1; w52 := G.4 * w7; w6 :=
    G.2 * G.4; w57 := G.1 * w6; w4 := G.2^2; w58 := w57 * w4; w59 := w52 * w58; 
    w26 := G.3^-1; w45 := G.2 * w26; w32 := G.1^-2; w60 := w45 * w32; w61 := w59
    * w60; w104 := w103 * w61; w105 := w104 * w61; w106 := w105 * G.1; w107 := 
    w106 * G.1; w108 := w107 * G.1; w1 := G.4 * G.3; w2 := G.5 * w1; w3 := w2 * 
    w1; w5 := G.3 * w4; w8 := w6 * w7; w9 := w8 * G.4; w11 := w9 * w10; w12 := 
    w5 * w11; w13 := w3 * w12; w14 := G.2 * G.1; w15 := w14 * w2; w16 := w15 * 
    w9; w17 := w9 * w16; w18 := w13 * w17; w19 := w18 * w5; w20 := G.5^-1; w21 
    := G.1^-1; w22 := w20 * w21; w23 := G.4^-1; w24 := G.2 * w23; w25 := w22 * 
    w24; w27 := w26 * w21; w28 := w20 * w23; w29 := w27 * w28; w30 := w25 * w29;
    w31 := G.2 * w20; w33 := w31 * w32; w34 := w23 * w21; w35 := w23 * G.2; w36 
    := w34 * w35; w37 := w33 * w36; w38 := w30 * w37; w39 := w19 * w38; w109 := 
    w108 * w39; return w109;
end function; 

// word for Delta for q = 1 mod 4 and q not equal to 9 
WordForDelta := function (d, q)
   function Special_OmegaStandardToPresentation (d, q)
      W := SLPGroup (5);
      s := W.1; t := W.2; delta := W.3; U := W.5; V := W.4;
      tau := d mod 4 eq 3 select t^V else (t^-1)^V;
      Z := s^V;
      p := Characteristic (GF(q));
      sigma := (tau^(Z * U), tau^((p + 1) div 2));
      return [(delta^V, U), Z, tau, sigma, U, V];
   end function;

   W := SLPGroup (6);
   // Delta2 = Delta^2 
   Delta2 := W.1; Z := W.2; tau := W.3; sigma := W.4; U := W.5; V := W.6;
   F := GF (q);
   e := Degree (F);
   w := PrimitiveElement (F);
   I := Integers ();
   E := sub<F | w^4>;
   c := Eltseq (E!(-w^3)); c := [I!x : x in c];
   b := Eltseq (E!(1 - w)); b := [I!x : x in b];
   a := Eltseq (E!(-w^-1 + 1)); a := [I!x : x in a];
   C := &*[(sigma^(Delta2^i * U))^c[i + 1] : i in [0..e - 1]];
   B := &*[(sigma^(Delta2^i * sigma^U))^b[i + 1] : i in [0..e - 1]];
   A := &*[(sigma^(Delta2^i))^a[i + 1] : i in [0..e - 1]];
   w_Delta := C * Delta2 * sigma^U * B * A;
   words := Special_OmegaStandardToPresentation (d, q);
   w_Delta := Evaluate (w_Delta, words);
   return w_Delta;
end function;

/* express presentation generators as words in standard generators */ 

function OmegaStandardToPresentation (d, q)
   W := SLPGroup (5);
   s := W.1; t := W.2; delta := W.3; U := W.5; V := W.4;

   tau := d mod 4 eq 3 select t^V else (t^-1)^V;            
   Z := s^V;
   p := Characteristic (GF(q));
   sigma := (tau^(Z * U), tau^((p + 1) div 2));

   // need to sort out Delta 
   if q mod 4 eq 3 then 
      Delta := U^2 * (delta^V, U)^((q + 1) div 4);
   elif q eq 9 then
      gens := [(delta^V, U), s^V, U, tau, sigma];
      Delta := SpecialWordForDelta ();
      Delta := Evaluate (Delta, gens);
   else 
      Delta := WordForDelta (d, q);
      // ensure Delta is in the correct SLPGroup 
      Delta := Evaluate (Delta, [W.i: i in [1..5]]);
   end if;

   return [Delta, Z, tau, sigma, U, V];
end function;

/* express standard generators as words in presentation generators */ 

function OmegaPresentationToStandard (d, q)
   W := SLPGroup (6);
   Delta := W.1; Z := W.2; tau := W.3; sigma := W.4; U := W.5; V := W.6;
   t := d mod 4 eq 3 select tau^(V^-1) else (tau^-1)^(V^-1);
   // return [s, t, delta, V, U]
   return [Z^(V^-1), t, (Z, Delta^-1)^(V^-1), V, U];
end function;
