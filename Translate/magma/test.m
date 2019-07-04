// usually subgroups chosen for coset enumeration are maximal of smallest index

SetGlobalTCParameters (: CosetLimit:=10^7, Hard, Print := 10^6);

import "sp.m": SpStandardToPresentation; 
import "minus.m": MinusStandardToPresentation;
import "plus.m": PlusStandardToPresentation;
import "circle.m": OmegaStandardToPresentation;
import "su.m": SUStandardToPresentation;

dim_limit := 20; // max dimension 
field_limit := 100; // max size of field  

// Presentation = false: presentation rewritten on standard generators
// Presentation = true: presentation listed in paper 
// Projective = true: presentation for group modulo its centre 
 
// do matrices satisfy presentation?
SLElements := function ();

for d in [2..dim_limit] do
   for q in [2..field_limit] do 
      if IsPrimePower (q) then 
      d, q;
      Q, R := ClassicalStandardPresentation ("SL", d, q: PresentationGenerators := false);
      S := ClassicalStandardGenerators ("SL", d, q);
      assert #Set (Evaluate (R, S)) eq 1;
      end if;
   end for;
end for;

return true;
end function;

// coset enumerations 

TestSL := function (a_list, b_list: Projective := false, Presentation := true)

for d in a_list do
   for q in b_list do
      DD := d; QQ := q;
      "\n D = ", d, "q = ", q;
      if d eq 2 then 
      Q,R:=ClassicalStandardPresentation ("SL", d, q: Projective := Projective, PresentationGenerators := false);
      else 
      Q,R:=ClassicalStandardPresentation ("SL", d, q: Projective := Projective, PresentationGenerators := Presentation);
      end if;
      F:=SLPToFP (Q, R); 

      f, p, e := IsPrimePower (q);
      U := F.1; V := F.2; tau := F.3; delta := F.4;

      if d eq 2 then 
         K := sub <F | tau, delta>;
      else 
         // max? subgroup containing SL(d - 1, q)
         K := sub <F | U, tau, V * U^(V^-1), delta, delta^(V^-1), tau^(V^-1)>;
      end if;

      I:=CosetImage(F, sub<F | K>);

      if Degree (I) lt 10^7 then 
      RandomSchreier (I);
      CompositionFactors (I);

      if d eq 2 then 
         assert Degree (I) eq q + 1;
      else 
         assert (q^d - 1) mod Degree (I) eq 0;
        // else assert Degree (I) eq (q^d - 1);
      end if;
      end if;
   end for;
end for;

return true;
end function;

SpElements := function ()

for d in [4..dim_limit by 2] do
   for q in [2..field_limit] do 
      if IsPrimePower (q) then 
      Q, R := ClassicalStandardPresentation ("Sp", d, q: PresentationGenerators := false);
      S := ClassicalStandardGenerators ("Sp", d, q);
      d, q;
      assert #Set (Evaluate (R, S)) eq 1;
      end if;
   end for;
end for;

return true;
end function;

TestSp := function (list_a, list_b: Projective := false, Presentation := true)

for d in list_a do 
   for q in list_b do 
      f, p, e := IsPrimePower (q);
      Q, R := ClassicalStandardPresentation ("Sp", d, q: 
                 Projective := Projective, PresentationGenerators := Presentation);
      F:=SLPToFP (Q, R);
      if Presentation then 
         Z := F.1; V := F.2; tau := F.3; delta := F.4; U := F.5; sigma := F.6; 
      else
         words := SpStandardToPresentation (d, q);
         X := Evaluate (words, [Q.i: i in [1..Ngens (Q)]]);
         phi := hom<Q -> F | [F.i: i in [1..Ngens (F)]]>;
         X := [phi (x): x in X];
         Z := X[1]; V := X[2]; tau := X[3]; delta := X[4]; U := X[5]; sigma := X[6]; 
      end if;
      if d eq 4 then 
         K:=sub<F | Z, tau, delta, delta^(V), sigma>;   
      else 
         m := (d div 2) - 1;
         K :=  sub<F | U, (V* U)^(V^-1), Z, tau, delta, delta^(V^(m)),
                          sigma, sigma^(V^(m))>;
      end if;

      I:=CosetImage (F, K);
      if Degree (I) lt 10^7 then 
      RandomSchreier (I);
      assert #I eq #Sp(d, q) or #I eq #Sp(d, q) div 2;
      CompositionFactors (I);
      end if;
   end for;
end for;

return true;
end function;

SUElements := function ()

for d in [3..dim_limit] do
   for q in [2..field_limit] do 
      if IsPrimePower (q) then 
         d, q;
         Q, R := ClassicalStandardPresentation ("SU", d, q: PresentationGenerators := false);
         S := ClassicalStandardGenerators ("SU", d, q);
         assert #Set (Evaluate (R, S)) eq 1;
      end if;
   end for;
end for;

return true;
end function;

TestSUEven := function (list_a, list_b: Projective:=false, Presentation := true)

for d in list_a do 
    assert IsEven (d);
    n := d div 2;
    for q in list_b do 
        Q,R:=ClassicalStandardPresentation ("SU", d, q: Projective:=Projective, PresentationGenerators := Presentation);
        F:=SLPToFP (Q, R);
        Z := F.1; V := F.2; tau := F.3; delta := F.4; U := F.5; sigma := F.6;  Delta := F.7;
        if d eq 4 then  
           // K := sub < F | [Z, V, U, delta, sigma, tau]>;
           // maximal x^a y^b L(2, q^2) 
           K := sub< F | V, tau, delta, sigma, Delta>;
        else 
           if Presentation then 
              if d eq 6 then 
                 K := sub<F | [Z, U, Delta^(V^-2), sigma^(V^(n - 2)), sigma]>;
              else 
                 K := sub<F | [Z, U, U^(V^-2) * V, Delta, Delta^(V^-2), delta, tau, sigma^(V^(n - 2)), sigma]>;
              end if;
           else 
              K := sub<F | [Z, U, U^(V^-2) * V, Delta, delta, tau, sigma^(V^(n - 2)), sigma]>;
           end if;
        end if;
        I:=CosetImage (F, K);
        if Degree (I) lt 10^7 then 
           RandomSchreier (I);
           CompositionFactors (I);
           //USECODE:assert #SU(d, q) mod #I eq 0; #SU(d, q) div #I in {1..Gcd (d, q + 1)};
        end if;
    end for;
end for;
return true;
end function;

TestSUOdd := function (list_a, list_b: Projective := false, Presentation := true)

for d in list_a do 
   assert IsOdd (d);
   n := d div 2;
   for q in list_b do 
      if d eq 3 then 
         Q,R:=ClassicalStandardPresentation ("SU", d, q: Projective := Projective, PresentationGenerators := true);
      else 
         Q,R:=ClassicalStandardPresentation ("SU", d, q: Projective := Projective, PresentationGenerators := Presentation);
      end if;
      F:=SLPToFP (Q, R);
      if d gt 3 then 
         X := [F.i: i in [1..Ngens (F)]];
         if not Presentation then 
            words := SUStandardToPresentation (d, q);
            X := Evaluate (words, [Q.i: i in [1..Ngens (Q)]]);
            phi := hom<Q -> F | [F.i: i in [1..7]]>;
            X := [phi (x): x in X];
         end if;
         Gamma := X[1]; t := X[2]; U := X[3]; V := X[4]; sigma := X[5]; tau := X[6]; v := X[7];
         if IsEven (q) then
            Z := t;
         else
            Z := (Gamma^-1)^((q^2 + q) div 2) * t;
         end if;
         Delta := Gamma * (Gamma^-1)^U;
      end if;

      if d eq 3 then
         // index q^3 + 1 
         // standard? K := sub<F | F.3, F.6, F.7>;
         K := sub<F | F.1, F.3>;
      elif d eq 5 then
         // p^k * SU(d-2, q)
         K := sub<F | Gamma, V * (U^V^-1), [x^U: x in [Gamma, t, tau, v]], sigma>;
      else
        // d >= 7
        // SU(d-1, q)
        // K := sub < F | [ Z, V, U, Delta, sigma, Gamma ]>;
        // p^k * SU(d-2, q)
        K := sub<F | Gamma, V*U, U^V, [x^U: x in [Gamma, t, tau, v]], sigma>;
     end if;

     I:=CosetImage (F, K);
     RandomSchreier (I);
     // assert Degree (I) eq q^d - 1;
     CompositionFactors (I);
     //USECODE:assert #SU(d, q) mod #I eq 0; #SU(d, q) div #I in {1..Gcd (d, q + 1)};
     // assert #I eq #SU(d, q) or #I eq #SU(d, q) div 2;
  end for;
end for;
return true;
end function;

TestSU := function (list_a, list_b: Presentation := true, Projective := false)
   for d in list_a do
      for q in list_b do 
         if IsEven (d) then 
            f := TestSUEven ([d], [q]: Presentation := Presentation, Projective := Projective);
         else 
            f := TestSUOdd ([d], [q]: Presentation := Presentation, Projective := Projective);
         end if;
      end for;
   end for;
return true;
end function;

PlusElements := function ()
for d in [4..dim_limit by 2] do
   for q in [2..field_limit] do 
      if IsPrimePower (q) then 
         d, q;
         Q, R := ClassicalStandardPresentation ("Omega+", d, q: PresentationGenerators := false);
         E := ClassicalStandardGenerators ("Omega+", d, q);
         assert #Set (Evaluate (R, E)) eq 1;
      end if;
   end for;
end for;
return true;
end function;

MinusElements := function ()
for d in [4..dim_limit by 2] do
   for q in [2..field_limit] do 
      if IsPrimePower (q) then 
         d, q;
         Q, R := ClassicalStandardPresentation ("Omega-", d, q: PresentationGenerators := false);
         E := ClassicalStandardGenerators ("Omega-", d, q);
         assert #Set (Evaluate (R, E)) eq 1;
      end if;
   end for;
end for;
return true;
end function;

OmegaElements := function ()
for d in [3..dim_limit by 2] do
   for q in [3..field_limit] do 
      if IsPrimePower (q) and IsOdd (q) then 
         d, q;
         Q, R := ClassicalStandardPresentation ("Omega", d, q: PresentationGenerators := false);
         E := ClassicalStandardGenerators ("Omega", d, q);
         assert #Set (Evaluate (R, E)) eq 1;
      end if;
   end for;
end for;
return true;
end function;

TestOmega := function (list_a, list_b: Presentation := true, Projective:=false)
for d in list_a do 
   assert IsOdd (d);
   for q in list_b do 
      assert IsOdd (q);
      Q, R := ClassicalStandardPresentation ("Omega", d, q: Projective := Projective, PresentationGenerators := Presentation);
      F := SLPToFP (Q, R);
      if d eq 3 then 
         K := sub< F | F.2, F.3>;
      else
         if Presentation eq false then 
            words := OmegaStandardToPresentation (d, q);
            X := Evaluate (words, [Q.i: i in [1..Ngens (Q)]]);
            phi := hom<Q -> F | [F.i: i in [1..Ngens (F)]]>;
            X := [phi (x): x in X];
            Delta := X[1]; Z := X[2]; tau := X[3]; sigma := X[4]; U := X[5]; V := X[6];
         else 
            Delta := F.1; Z := F.2; tau := F.3; sigma := F.4; U := F.5; V := F.6;
         end if;
         // SOPlus (d - 1, q).2 
         K := sub < F | Delta, Z, sigma, U, V>;
      end if;
      I := CosetImage (F, K);
      RandomSchreier (I);
      CompositionFactors (I);
   end for;
end for;
return true;
end function;

TestMinus := function (list_a, list_b: Presentation := true, Projective := false)

for d in list_a do 
   assert IsEven (d);
   for q in list_b do 
      Q, R := ClassicalStandardPresentation ("Omega-", d, q: PresentationGenerators := Presentation, Projective:=Projective);
      F:=SLPToFP (Q, R);
      if d eq 4 then 
          K := sub< F | [F.i: i in [2..5]]>;
      else 
         if Presentation then 
            z := F.1; sigma := F.3; tau := F.2; U := F.5; Delta := F.4; 
            if d eq 6 then V := F.0; else V := F.6; end if;
         else 
            words := MinusStandardToPresentation (d, q);
            X := Evaluate (words, [Q.i: i in [1..Ngens (Q)]]);
            phi := hom<Q -> F | [F.i: i in [1..Ngens (F)]]>;
            X := [phi (x): x in X];
            z := X[1]; sigma := X[3]; tau := X[2]; U := X[5]; Delta := X[4];
            if d eq 6 then V := X[1]^0; else V := X[6]; end if;
         end if;
         if d eq 6 then 
            K := sub< F | Delta, sigma, tau, Delta^U, V * U^-1>;  
         else 
            K := sub< F | Delta, sigma, tau, Delta^U, z^U, tau^U,  U^V, V * U^-1>;
         end if;
      end if;
      I := CosetImage (F, K);
      RandomSchreier (I);
      CompositionFactors (I);
   end for;
end for;

return true;
end function;

TestPlusOdd := function (list_a, list_b: Presentation := true, Projective:=false)

for d in list_a do 
   assert IsEven (d);
   for q in list_b do 
       assert IsOdd (q);
       Q, R := ClassicalStandardPresentation ("Omega+", d, q: PresentationGenerators := Presentation, Projective := Projective);
       F := SLPToFP (Q, R);
       if d eq 4 then 
          K := sub<F | [F.i: i in [1,3,5,6,7]]>;
       else 
          if Presentation then 
             Delta := F.1; sigma := F.2; Z := F.3; U := F.4; V := F.5;
          else
             words := PlusStandardToPresentation (d, q);
             X := Evaluate (words, [Q.i: i in [1..Ngens (Q)]]);
             phi := hom<Q -> F | [F.i: i in [1..Ngens (F)]]>;
             X := [phi (x): x in X];
             Delta := X[1]; sigma := X[2]; Z := X[3]; U := X[4]; V := X[5];
          end if;
          K := sub<F | U^V, Z^V, sigma^V, Delta^V, (sigma^(Z^V))^V, V*U, sigma, Delta>;
       end if;
       I := CosetImage (F, K);
       RandomSchreier (I);
       CompositionFactors (I);
    end for;
end for;

return true;
end function;

TestPlusEven := function (list_a, list_b: Presentation := true) 

for d in list_a do 
   assert IsEven (d);
   for q in list_b do 
      assert IsEven (q);
      Q, R := ClassicalStandardPresentation ("Omega+", d, q: PresentationGenerators := Presentation);
      F:=SLPToFP (Q, R);
      if d eq 4 then 
          K := sub<F | [F.i: i in [1,3,5,6,7]]>;
      else
         if Presentation then 
            delta := F.1; sigma := F.2; Z := F.3; U := F.4; V := F.5;
         else 
            words := PlusStandardToPresentation (d, q);
            X := Evaluate (words, [Q.i: i in [1..Ngens (Q)]]);
            phi := hom<Q -> F | [F.i: i in [1..Ngens (F)]]>;
            X := [phi (x): x in X];
            delta := X[1]; sigma := X[2]; Z := X[3]; U := X[4]; V := X[5];
         end if;
         Delta := delta * (delta^-1)^U;
         K:=sub<F | U^V, Z^V, sigma^V, Delta^V, (sigma^(Z^V))^V, V* U, sigma, Delta>;
      end if;
      I := CosetImage (F, K);
      RandomSchreier (I);
      CompositionFactors (I);
   end for;
end for;
return true;
end function;

TestPlus := function (list_a, list_b: Presentation := true, Projective := false)
   for d in list_a do
      for q in list_b do 
         if IsEven (q) then 
            f := TestPlusEven ([d], [q]: Presentation := Presentation);
         else 
            f := TestPlusOdd ([d], [q]: Presentation := Presentation, Projective := Projective);
         end if;
      end for;
   end for;
return true;
end function;
