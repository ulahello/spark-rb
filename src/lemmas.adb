pragma Ada_2022;

package body Lemmas with SPARK_Mode => On is

   function Is_Power_Of_Two (N : Natural) return Boolean
   is (case N is
      when 0 => False,
      when 1 => True,
      when others => N mod 2 = 0
         and then Is_Power_Of_Two (N / 2));

   procedure Lemma_Exp2_Implies_Power2 (K, N : Natural) is
   begin
      if K = 0 then
         pragma Assert (Is_Power_Of_Two (N));
         return;
      end if;
      Lemma_Exp2_Implies_Power2 (K - 1, N / 2);
      pragma Assert (N / 2 = 2 ** (K - 1));
   end Lemma_Exp2_Implies_Power2;

   procedure Lemma_Mod_Def (A, B, M, K : Big_Integer)
   is
   begin
      pragma Assume (A mod M = B mod M, "sorry");
   end Lemma_Mod_Def;

   procedure Lemma_Mod_Def_Converse (A, B, M, K : Big_Integer)
   is
   begin
      pragma Assume (A = B + K*M, "sorry");
   end Lemma_Mod_Def_Converse;

   procedure Lemma_Mod_Idempotent (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Nop (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Preserves_Eq (A, B, M : Big_Integer) is null;

   procedure Lemma_Mod_Add_Simp (A, B, M : Big_Integer) is

      procedure Lemma_Mod_Add_Nop (A, M : Big_Integer)
        with Ghost,
             Pre => M /= 0,
             Post => (A + M) mod M = A mod M
                     and then (A - M) mod M = A mod M
      is
      begin
         Lemma_Mod_Def (A, A + M, M, -1);
         Lemma_Mod_Def (A, A - M, M, 1);
      end Lemma_Mod_Add_Nop;

      procedure Lemma_Mod_Add_Simp_Nonneg (A, B, M : Big_Integer)
        with Ghost,
             Pre => 0 < M and then 0 <= B,
             Post => (A + B mod M) mod M = (A + B) mod M,
             Subprogram_Variant => (Decreases => B)
      is
      begin
         if B < M then
            Lemma_Mod_Nop (B, M);
            Lemma_Mod_Preserves_Eq (A + B mod M, A + B, M);
         else
            Lemma_Mod_Add_Simp_Nonneg (A, B - M, M);
            Lemma_Mod_Add_Nop (B, M);
            Lemma_Mod_Add_Nop (A + B, M);
            pragma Assert ((A + B mod M) mod M = (A + B) mod M);
         end if;
      end Lemma_Mod_Add_Simp_Nonneg;

      procedure Lemma_Mod_Add_Simp_Neg (A, B, M : Big_Integer)
        with Ghost,
             Pre => 0 < M and then 0 < B,
             Post => (A + (-B) mod M) mod M = (A - B) mod M,
             Subprogram_Variant => (Decreases => B) --  can't use Increase with Big_Integer, so manually negate B
      is
      begin
         if 0 <= -B + M then
            Lemma_Mod_Add_Simp_Nonneg (A, -B + M, M);
            Lemma_Mod_Add_Nop (-B, M);
            Lemma_Mod_Add_Nop (A - B, M);
            pragma Assert ((A + (-B) mod M) mod M = (A - B) mod M);
         else
            Lemma_Mod_Add_Simp_Neg (A, B - M, M);
            Lemma_Mod_Add_Nop (-B, M);
            Lemma_Mod_Add_Nop (A - B, M);
            pragma Assert ((A + (-B) mod M) mod M = (A - B) mod M);
         end if;
      end Lemma_Mod_Add_Simp_Neg;

   begin
      if 0 < M then
         if 0 <= B then
            Lemma_Mod_Add_Simp_Nonneg (A, B, M);
            pragma Assert ((A + B mod M) mod M = (A + B) mod M);
         else
            Lemma_Mod_Add_Simp_Neg (A, -B, M);
            pragma Assert ((A + B mod M) mod M = (A + B) mod M);
         end if;
      else
         pragma Assume ((A + B mod M) mod M = (A + B) mod M, "sorry");
      end if;
   end Lemma_Mod_Add_Simp;

   procedure Lemma_Mod_Mul_Simp (A, B, M : Big_Integer) is
   begin
      Lemma_Mod_Idempotent (B, M);
      Lemma_Mod_Scale_Compat (B, B mod M, A, M);
   end Lemma_Mod_Mul_Simp;

   procedure Lemma_Mod_Trans_Compat (A, B, K, M : Big_Integer) is
      procedure Lemma_Mod_Trans_Compat_Eq (A, B, K, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then A mod M = B mod M,
             Post => (A + K) mod M = (B + K) mod M
      is
      begin
         pragma Assert (K + (A mod M) = K + (B mod M));
         pragma Assert ((K + (A mod M)) mod M = (K + (B mod M)) mod M);
         Lemma_Mod_Add_Simp (K, A, M);
         Lemma_Mod_Add_Simp (K, B, M);
         pragma Assert ((A + K) mod M = (B + K) mod M);
      end Lemma_Mod_Trans_Compat_Eq;

      procedure Lemma_Mod_Bounded_Add_Can_Break_Eq (A, K, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then 0 < K and then K < M, --  TODO: implies M positive
             Post => (A mod M /= (A + K) mod M)
      is
      begin
         pragma Assert (0 < M);
         pragma Assume (A mod M /= (A + K) mod M, "sorry");
      end Lemma_Mod_Bounded_Add_Can_Break_Eq;

      procedure Lemma_Mod_Trans_Can_Break_Eq (A, B, K, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then A mod M = B mod M,
             Post => (if K mod M = 0 then A mod M = (B + K) mod M
                                     else A mod M /= (B + K) mod M)
      is
      begin
         if K mod M = 0 then
            Lemma_Mod_Add_Simp (B, K, M);
            pragma Assert ((B + K) mod M = B mod M);
            pragma Assert (A mod M = (B + K) mod M);
         else
            pragma Assert (K /= 0);
            Lemma_Mod_Add_Simp (B, K, M);
            Lemma_Mod_Add_Simp (K, B, M);
            pragma Assert ((B + K) mod M = (B + K mod M) mod M);
            pragma Assert (B + K /= B);
            pragma Assert (B mod M + K /= B mod M);
            if 0 < M then
               pragma Assert (0 < K mod M and then K mod M < M);
               Lemma_Mod_Bounded_Add_Can_Break_Eq (B, K mod M, M);
               pragma Assert ((B + K) mod M /= B mod M);
               pragma Assert (A mod M /= (B + K) mod M);
            else
               pragma Assert (A mod M /= (B + K) mod M);
            end if;
         end if;
      end Lemma_Mod_Trans_Can_Break_Eq;

      procedure Lemma_Mod_Trans_Compat_Neq (A, B, K, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then A mod M /= B mod M,
             Post => (A + K) mod M /= (B + K) mod M
      is
         Ap : constant Big_Integer := A mod M;
         Bp : constant Big_Integer := B mod M;
         D : constant Big_Integer := Bp - Ap;
      begin
         pragma Assert (D /= 0);
         pragma Assert (Ap + D = Bp);
         pragma Assert (K + Ap + D = K + Bp);
         pragma Assert ((K + Ap + D) mod M = (K + Bp) mod M);
         Lemma_Mod_Add_Simp (K + D, A, M);
         pragma Assert ((K + D + A mod M) mod M = (K + D + A) mod M);
         pragma Assert ((K + D + Ap) mod M = (K + D + A mod M) mod M);
         pragma Assert ((K + D + Ap) mod M = (K + D + A) mod M);
         Lemma_Mod_Add_Simp (K, B, M);
         pragma Assert ((K + B mod M) mod M = (K + B) mod M);
         pragma Assert ((K + Bp) mod M = (K + B mod M) mod M);
         pragma Assert ((K + Bp) mod M = (K + B) mod M);
         pragma Assert ((K + A + D) mod M = (K + B) mod M);

         pragma Assert (D mod M /= 0);
         pragma Assert ((-D) mod M /= 0);

         Lemma_Mod_Trans_Can_Break_Eq (K + B, K + A + D, -D, M);
         pragma Assert ((K + B) mod M /= ((K + A + D) + (-D)) mod M);

         pragma Assert ((A + K) mod M /= (B + K) mod M);
      end Lemma_Mod_Trans_Compat_Neq;

   begin
      if A mod M = B mod M then
         Lemma_Mod_Trans_Compat_Eq (A, B, K, M);
         pragma Assert ((A + K) mod M = (B + K) mod M);
      else
         Lemma_Mod_Trans_Compat_Neq (A, B, K, M);
         pragma Assert ((A + K) mod M /= (B + K) mod M);
      end if;
   end Lemma_Mod_Trans_Compat;

   procedure Lemma_Mod_Scale_Compat (A, B, K, M : Big_Integer) is
      L : constant Big_Integer := (A - B) / M;
   begin
      Lemma_Mod_Def_Converse (A, B, M, L);
      Lemma_Mod_Def (K*A, K*B, M, K*L);
   end Lemma_Mod_Scale_Compat;

   procedure Lemma_Mod_Composite (A, B, M, N : Big_Integer) is
      K : constant Big_Integer := (A - B) / (M * N);
   begin
      Lemma_Mod_Def_Converse (A, B, M*N, K);

      --  Using the definition of mod, once we've found a K such that
      --  A = B + MNK, we can reassociate MNK and trivially prove the
      --  postcondition.
      pragma Assert (A = B + M*N*K);
      Lemma_Mod_Def (A, B, M, N*K);
      Lemma_Mod_Def (A, B, N, M*K);
   end Lemma_Mod_Composite;

   procedure Lemma_Push_Increases_Length (R, W, C, N, Np, dW : Big_Integer) is
   begin
      --  By definition,
      --  N' ≡ ((dW + W) mod 2C - R) mod 2C
      --     ≡ (dW + W - R)          mod 2C,
      --  Substituting W - R, we get that N' ≡ N + dW mod 2C, and
      --  with lengths bounded less than C, that they are equal.
      Lemma_Mod_Add_Simp (-R, W + dW, 2*C);
      Lemma_Mod_Trans_Compat (Np, W - R + dW, -dW, 2*C);
      Lemma_Mod_Nop (N, 2*C);
      Lemma_Mod_Nop (Np - dW, 2*C);
   end Lemma_Push_Increases_Length;

   procedure Lemma_Pop_Decreases_Length (R, W, C, N, Np, dR : Big_Integer) is
   begin
      --  Np ≡ W - (R + dR) mod 2C   mod 2C
      --     ≡ W - R - dR            mod 2C
      --     ≡ (-R - dR) mod 2C + W  mod 2C
      --  This matches the form that the Push lemma expects.
      Lemma_Mod_Mul_Simp (-1, R + dR, 2*C);
      Lemma_Mod_Trans_Compat (-R - dR, -(R + dR) mod (2*C), W, 2*C);
      Lemma_Mod_Add_Simp (W, -R - dR, 2*C);
      Lemma_Push_Increases_Length (-W, -R, C, N, Np, -dR);
   end Lemma_Pop_Decreases_Length;

   procedure Lemma_Pop_Shifts_Back_Elements (R, Rp, C, I, dR : Big_Integer) is
   begin
      Lemma_Mod_Trans_Compat (Rp, R + dR, I, 2*C);
      Lemma_Mod_Composite (Rp + I, R + dR + I, 2, C);
   end Lemma_Pop_Shifts_Back_Elements;

end Lemmas;
