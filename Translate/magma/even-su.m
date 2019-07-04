import "sn.m": PresentationForSn;
import "sl2q.m": PresentationForSL2;

// this agrees with paper definition of psi
EvenSUGenerators := function (d, q)
   assert IsEven (d);
   S := ClassicalStandardGenerators ("SU", d, q);
   Z := S[1]; Z := Z^-1;
   V := S[2];
   tau := S[3]; tau := tau^-1;
   delta := S[4]; delta := delta^-1;
   U := S[5];
   sigma := S[6]; sigma := sigma^(V^2);
   Delta := S[7]^(V^2); Delta := Delta^-1;
   T := [Z, V, tau, delta, U, sigma, Delta];
   return T;
end function;

Thm71 := function (n, q) 
   Rels := [];
   if n eq 2 then 
      F := SLPGroup (2);
      Delta := F.1; U := F.2; 
      R := [];
      Append (~Rels, U^2 = 1);
   else 
      F := SLPGroup (3);
      Delta := F.1; U := F.2; V := F.3; 

      S, R := PresentationForSn (n);
      tau := hom<S-> F | U, V>;
      R := [tau (r): r in R];

      if n gt 3 then 
         Append (~Rels, (Delta, U^(V^2)) = 1);
         Append (~Rels, (Delta, Delta^(V^2)) = 1);
      end if;
      if n gt 4 then 
         Append (~Rels, (Delta, V * U * U^V) = 1);
      end if;
      Append (~Rels, Delta * Delta^V = Delta^(V * U));
      Append (~Rels, (Delta, Delta^V) = 1);
   end if;
   OMIT := true;
   if not OMIT then 
      Append (~Rels, Delta^U = Delta^-1);
      Append (~Rels, Delta^(q^2 - 1) = 1);
   end if;
   
   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R;
   return F, Rels;
end function;
  
OrderThm71 := function (n, q)
   return (q^2 - 1)^(n - 1) * Factorial (n);
end function;

Thm72 := function (n, q)
   F := SLPGroup (4);
   Delta := F.1; U := F.2; V := F.3; delta := F.4;
   Rels := [];

   S, R := Thm71 (n, q);
   if n eq 2 then 
      Append (~Rels, U = V); 
      tau := hom<S-> F | Delta, U>;
   else 
      tau := hom<S-> F | Delta, U, V>;
   end if;
   R := [tau (r): r in R];

   OMIT := true;
   if not OMIT then 
      Append (~Rels, delta^(q - 1) = 1);
   end if;
   if n gt 2 then 
      Append (~Rels, (delta, U^V) = 1);
      Append (~Rels, (delta, Delta^V) = 1);
   end if;
   Append (~Rels, (delta, Delta) = 1);
   if n gt 3 then 
      Append (~Rels, (delta, V * U) = 1);
   end if;
   Append (~Rels, Delta^(q + 1) = delta * (delta^-1)^U);

   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R;
   return F, Rels;
end function;

OrderThm72 := function (n, q)
   return (q - 1) * (q^2 - 1)^(n - 1) * Factorial (n);
end function;

SU_PresentationForN := function (n, q)
   F := SLPGroup (5);
   Delta := F.1; U := F.2; V := F.3; delta := F.4; Z := F.5;

   S, R := Thm72 (n, q);
   tau := hom<S-> F | Delta, U, V, delta>;
   R := [tau (r): r in R];

   Rels := [];
   OMIT := true;
   if not OMIT then 
      if IsOdd (q) then 
         Append (~Rels, Z^2 = delta^((q - 1) div 2));
      else 
         Append (~Rels, Z^2 = 1);
      end if;
      Append (~Rels, delta^Z = delta^-1); 
   end if;

   if n gt 2 then 
      Append (~Rels, (Z, U^V) = 1);
      Append (~Rels, (Z, Delta^V) = 1);
   end if;
   if n gt 3 then 
      Append (~Rels, (Z, V * U) = 1);
   end if;

   Append (~Rels, (Z, Z^U) = 1);
   Append (~Rels, delta = (Delta^-1, Z));

   if n eq 2 then Append (~Rels, (delta, Z^U) = 1); end if;

   Rels := [LHS (r) * RHS (r)^-1: r in Rels] cat R;
   return F, Rels;
end function;

OrderSU_N := function (n, q)
   return 2^n * (q - 1) * (q^2 - 1)^(n - 1) * Factorial (n);
end function;

EvenSUPresentation := function (d, q)
   assert IsPrimePower (q);
   assert IsEven (d) and d gt 2;
   n := d div 2;

   f, p, e := IsPrimePower (q);

   F := SLPGroup (7);
   Z := F.1; V := F.2; tau := F.3; delta := F.4; U := F.5; sigma := F.6; Delta := F.7;
   
   R := [];

   S, R4 := SU_PresentationForN (n, q);
   eta := hom<S-> F | Delta, U, V, delta, Z>;
   R4 := [eta (r): r in R4];

   // centraliser of sigma 
   if n gt 3 then Append (~R, (U^(V^2), sigma) = 1); end if;
   if n gt 4 then Append (~R, (V * U * U^V, sigma) = 1); end if;
   if n gt 3 and IsOdd (q) then Append (~R, (Delta^(V^2), sigma) = 1); end if;
   if n eq 3 and IsOdd (q) then Append (~R, (delta^(V^2), sigma) = 1); end if;
   if n gt 2 then 
      Append (~R, (Z^(V^2), sigma) = 1); 
      Append (~R, (Delta * (Delta^2)^V, sigma) = 1); 
   end if;
   if n eq 2 then 
      if IsEven (q) then Append (~R, (delta * delta^U, sigma) = 1); 
      else Append (~R, (Delta^((q + 1) div 2) * delta^-1, sigma) = 1); end if;
   end if;
   Append (~R, (Z * U * Z^-1, sigma) = 1); 

   // centraliser of tau 
   if n gt 2 then Append (~R, (U^V, tau) = 1); end if;
   if n eq 2 and IsOdd (q) then Append (~R, (delta^U, tau) = 1); end if;
   if n gt 2 then Append (~R, (Delta^V, tau) = 1); end if;
   // V*U is needed to generate centraliser of tau but relation not needed
   OMIT := true;
   if not OMIT then 
      if n gt 3 then Append (~R, (V * U, tau) = 1); end if;
   end if;
   Append (~R, (Z^U, tau) = 1); 
   Append (~R, (Delta^2 * delta^-1, tau) = 1); 

   S, R1 := PresentationForSL2 (p, e);
   if e eq 1 then 
      phi := hom<S-> F | tau, Z>;
      // need to express delta as word in <tau, Z> = SL(2, p)
      w := PrimitiveElement (GF(p));
      I := Integers ();
      x := I!(w^-1) - 1;
      y := I!(w^-2 - w^-1);
      Append (~R, delta = tau^-1 * (tau^x)^Z * tau^(I!w) * (tau^-y)^Z);
   else
      phi := hom<S-> F | delta, tau, Z>;
   end if;
   R1 := [phi (r): r in R1];

   W := IsEven (q) select U else U * Z^2;
   S, R2 := PresentationForSL2 (p, 2 * e);
   phi := hom<S-> F | Delta, sigma, W>;
   R2 := [phi (r): r in R2];
   
   // Steinberg relations 
   R3 := [];
   Append (~R3, (sigma, tau) = 1);

   if IsEven (q) then 
      Append (~R3, (sigma, sigma^Z) = 1);
   else 
      Append (~R3, (sigma, sigma^Z) = (tau^2)^(Z * U));
   end if;

   if (q ne 3) then 
      E<w> := GF(q^2);
      w0 := w^(q+1);
      a := w^(2 * q) + w^2;
      m := Log (w0, a);
      Append (~R3, (sigma^Delta, sigma^Z) = tau^(Z * U * Delta^m));
   else
      Append (~R3, (sigma^Delta, sigma^Z) = 1);
   end if;

   Append (~R3, (sigma, tau^Z) = sigma^Z * (tau^-1)^(Z * U));

   // additional relation needed for SU(6, 2) -- probably only #2 required 
   if (n eq 3 and q eq 2) then
      Append (~R3, (sigma, sigma^(U^V * Delta)) = 1);
      Append (~R3, (sigma, sigma^(V * Delta)) = sigma^(V * U * Delta^-1));
   end if;

   if n gt 2 then 
      Append (~R3, (sigma, sigma^(U^V)) = 1);
      Append (~R3, (sigma, sigma^V) = sigma^(V * U));
   end if;
   if n lt 4 then  Append (~R3, (tau, tau^U) = 1); end if;
   if n eq 3 then Append (~R3, (tau, sigma^V) = 1); end if;
   if n gt 3 then Append (~R3, (sigma, sigma^(V^2)) = 1); end if;

   if n eq 2 and q eq 3 then 
      Append (~R3, tau = ((sigma^-1)^(U * Z), sigma)^Delta);
   end if;

   Rels := [LHS (r) * RHS (r)^-1: r in R cat R3] cat R1 cat R2 cat R4; 
   return F, Rels;
end function;
