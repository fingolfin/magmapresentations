// presentation for Sym (d) defined on (1, 2) and (1..n)
PresentationForSn := function (d: SLP := true)
   F := FreeGroup (2);
   U := F.1;  // (1, 2) 
   V := F.2;  // (1,2, ..., d)
   Rels := [];
   Append (~Rels, 1=U^2);
   if d eq 1 then 
      Rels := [U, V];
      if not SLP then return quo< F | U, V>; end if;
   elif d eq 2 then
      Rels := [U = V, U^2 = 1];
      if not SLP then return quo< F | U = V, U^2>; end if;
   else 
      Append (~Rels, 1=V^d);
      Append (~Rels, 1=(U*V)^(d-1));
      Append (~Rels, 1=(U, V)^3);
   end if;
   for i in [2..(d div 2)] do Append (~Rels, 1=(U, V^i)^2); end for;
   if not SLP then 
      return quo<F | Rels>, _;
   else 
      S := SLPGroup (2);
      tau := hom <F-> S | [S.1, S.2]>;
      Rels := [LHS (r) * RHS (r)^-1: r in Rels];
      Rels := [tau (r): r in Rels];
      return S, Rels;
   end if;
end function;

PresentationForAn := function (d)
   S := PresentationForSn (d: SLP := false);
   if IsEven (d) then
      W := S.1 * S.2;
      T := (S.2 * S.2^S.1)^-1;
   end if;
   A := sub< S | W, T>;
   Rewrite (S, ~A: Simplify := false); 
   
   S := Sym (d);
   W := S.1 * S.2;
   T := (S.2 * S.2^S.1)^-1;
   A := sub< S | W, T>;
   A := FPGroup (A);
   Rels := Relations (A);
   S := SLPGroup (2);
   tau := hom <A-> S | [S.1, S.2]>;
   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   Rels := [tau (r): r in Rels];
   return S, Rels;
end function;

// presentation for Alt (n) 
PresentationForAn := function (n)
   if IsOdd (n) then
       /* n odd: a=(1,2,3), b=(1,2,...,n), */
       A := Group <a, b | a^3, b^n, (a*b^2)^((n-1) div 2),
                           [((b*a)^j*b^-j)^2 : j in [2..n - 2]]>;
   else
      /* n even: a=(1,2,3), b=(2,...,n) */
      A := Group < a, b | a^3, b^(n-1), (b^2*a^-1)^(n div 2), (b*a^-1)^(n-1),
        [((b^-1*a*b^-1)^j*(b^2*a^-1)^j)^2 : j in [1..n div 2 - 1]],
        [((b^-1*a*b^-1)^j*(a^-1*b^2)^j*a^-1)^2 : j in [1.. n div 2 - 2]]>;
   end if;

   Rels := Relations (A);
   S := SLPGroup (2);
   tau := hom <A-> S | [S.2, S.1]>;
   Rels := [LHS (r) * RHS (r)^-1: r in Rels];
   Rels := [tau (r): r in Rels];
   return S, Rels;
end function;
