SignedOdd := function (d)
   S := SLPGroup (2);
   u := S.1; v := S.2;
   Rels := [u^4, (u^2)^(v * u) * u^2 * (u^2)^v, v^d, (u * v)^(d-1),  
            (u * v^-1 * u * v)^3]
        cat [(u, v^-j * u * v^j): j in [2 .. d div 2]];
   return S, Rels;
end function;

SignedEven := function (d)
   S := SLPGroup (2);
   u := S.1; v := S.2;

   if d eq 2 then
      Rels := [u^4, u * v^-1];
      return S, Rels;
   end if;

   Rels := [u^4,  (u^2)^(v * u) * u^2 * (u^2)^v, 
            (u * v^-1 * u * v)^3] 
       cat [(u, v^-j * u * v^j): j in [2 .. d div 2]]; 
   R := [v^d = (u * v)^(d-1), 
         (v^d, u) = 1, v^(2 *d) = 1];
   Rels cat:= [LHS (r) * RHS (r)^-1: r in R];
   return S, Rels;
end function;

// presentation for group of signed permutation matrices of rank d and det 1
SignedPermutations := function (d)
   assert d gt 1; 
   if IsEven (d) then return SignedEven (d); else return SignedOdd (d); end if;
end function;

OrderSigned := function (d)
   return 2^(d - 1) * Factorial (d);
end function;
