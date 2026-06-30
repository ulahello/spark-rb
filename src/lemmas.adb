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

   procedure Lemma_Mod_Diff_Def (A, B, M, K : Big_Integer) is null;

   procedure Lemma_Mod_Negate (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Diff_Divides (A, B, M : Big_Integer) is

      procedure Lemma_Mod_Diff_Negate_Divisor (A, B, M : Big_Integer)
        with Ghost,
             Pre => M /= 0,
             Post => ((A - B) mod M = 0) = ((A - B) mod (-M) = 0)
      is
         K : constant Big_Integer := (A - B)/M;
         Kp : constant Big_Integer := (A - B)/(-M);
      begin
         Lemma_Mod_Diff_Def (A, B, M, K);
         Lemma_Mod_Diff_Def (A, B, -M, Kp);
         pragma Assert (K * M = Kp * (-M));
      end Lemma_Mod_Diff_Negate_Divisor;

      procedure Lemma_Mod_Diff_Negate_Dividend (A, B, M : Big_Integer)
        with Ghost,
             Pre => M /= 0,
             Post => ((A - B) mod M = 0) = ((B - A) mod M = 0)
      is
      begin
         Lemma_Mod_Diff_Negate_Divisor (A, B, M);
      end Lemma_Mod_Diff_Negate_Dividend;

      procedure Lemma_Div (A, B, M: Big_Integer)
        with Ghost,
             Pre => M /= 0 and then A = B * M,
             Post => A/M = B and then (A/M)*M = B*M
      is
      begin
         null;
      end Lemma_Div;

      procedure Lemma_Frac_Split (A, B, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then A mod M = 0 and then B mod M = 0,
             Post => (A + B)/M = A/M + B/M
      is
      begin
         Lemma_Mod_Diff_Def (A, 0, M, A/M);
         Lemma_Mod_Diff_Def (B, 0, M, B/M);
      end Lemma_Frac_Split;

      procedure Helper_Nonneg (N, M : Big_Integer)
        with Ghost,
             Pre => 0 < M and then 0 <= N,
             Post => (N - (N mod M)) mod M = 0,
             Subprogram_Variant => (Decreases => N)
      is
      begin
         if N < M then
            pragma Assert (N = N mod M);
            return;
         end if;
         Helper_Nonneg (N - M, M);
         pragma Assert ((N - M - (N - M) mod M) mod M = 0);
         pragma Assert ((N - (N mod M)) mod M = 0);
      end Helper_Nonneg;

      procedure Helper (N, M : Big_Integer)
        with Ghost,
             Pre => M /= 0,
             Post => (N - (N mod M)) mod M = 0
      is
      begin
         if 0 <= M then
            if 0 <= N then
               Helper_Nonneg (N, M);
               pragma Assert ((N - (N mod M)) mod M = 0);
            else
               Helper_Nonneg (-N, M);
               Lemma_Mod_Diff_Negate_Dividend (-N, (-N) mod M, M);
               Lemma_Mod_Negate (-N, M);
               pragma Assert ((N + (-N) mod M) mod M = 0);
               pragma Assert ((N - (N mod M)) mod M = 0);
            end if;
         else
            if 0 <= N then
               Helper_Nonneg (N, -M);
               Lemma_Mod_Diff_Negate_Divisor (N, N mod (-M), M);
               pragma Assert ((N - (N mod M)) mod M = 0);
            else
               Helper_Nonneg (-N, -M);
               pragma Assert ((N - (N mod M)) mod M = 0);
            end if;
         end if;
      end Helper;

      procedure Forward (A, B, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then (A mod M = B mod M),
             Post => (A - B) mod M = 0
      is
         K : constant Big_Integer := (A - B) / M;
         La : constant Big_Integer := (A - (A mod M)) / M;
         Lb : constant Big_Integer := (B - (B mod M)) / M;
      begin
         Helper (A, M);
         Helper (B, M);
         Lemma_Div (A - (A mod M), La, M);
         Lemma_Div (B - (B mod M), Lb, M);
         pragma Assert (La*M = A - (A mod M));
         pragma Assert (Lb*M = B - (B mod M));
         Lemma_Mod_Negate (Lb*M, M);
         Lemma_Frac_Split (La*M, -Lb*M, M);
         pragma Assert (K = La - Lb);
         Lemma_Mod_Diff_Def (A, B, M, K);
      end Forward;

      procedure Backward (A, B, M : Big_Integer)
        with Ghost,
             Pre => M /= 0 and then (A - B) mod M = 0,
             Post => A mod M = B mod M
      is
         K : constant Big_Integer := (A - B) / M;
         La : constant Big_Integer := (A - (A mod M)) / M;
         Lb : constant Big_Integer := (B - (B mod M)) / M;
         Lp : constant Big_Integer := Lb + K - La;
      begin
         pragma Assert (A = B + K*M);
         Helper (A, M);
         Helper (B, M);
         pragma Assert (A = (A mod M) + La*M);
         pragma Assert (B = (B mod M) + Lb*M);
         pragma Assert (A mod M = B mod M + Lb*M + K*M - La*M);
         pragma Assert (Lb*M + K*M - La*M = Lp*M);
         pragma Assert (Lp*M = 0);
         pragma Assert (A mod M = B mod M);
      end Backward;

   begin
      if A mod M = B mod M then
         Forward (A, B, M);
      end if;
      if (A - B) mod M = 0 then
         Backward (A, B, M);
      end if;
   end Lemma_Mod_Diff_Divides;

   procedure Lemma_Mod_Def (A, B, M, K : Big_Integer) is
   begin
      Lemma_Mod_Diff_Def (A, B, M, K);
      Lemma_Mod_Diff_Divides (A, B, M);
   end Lemma_Mod_Def;

   procedure Lemma_Mod_Def_Helper (A, B, M, K : Big_Integer) is null;

   procedure Lemma_Mod_Idempotent (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Nop (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Add_Simp (A, B, M : Big_Integer) is
   begin
      Lemma_Mod_Idempotent (B, M);
      Lemma_Mod_Trans_Compat (B, B mod M, A, M);
   end Lemma_Mod_Add_Simp;

   procedure Lemma_Mod_Mul_Simp (A, B, M : Big_Integer) is
   begin
      Lemma_Mod_Idempotent (B, M);
      Lemma_Mod_Scale_Compat (B, B mod M, A, M);
   end Lemma_Mod_Mul_Simp;

   procedure Lemma_Mod_Trans_Compat (A, B, K, M : Big_Integer) is
      L : constant Big_Integer := (A - B) / M;
   begin
      Lemma_Mod_Def (A, B, M, L);
      Lemma_Mod_Def (A + K, B + K, M, L);
      if A mod M = B mod M then
         --  A = B + LM, so A + K = (B + K) + LM.
         pragma Assert ((A + K) mod M = (B + K) mod M);
      else
         -- The same reasoning as above applies for the inequation.
         pragma Assert ((A + K) mod M /= (B + K) mod M);
      end if;
   end Lemma_Mod_Trans_Compat;

   procedure Lemma_Mod_Scale_Compat (A, B, K, M : Big_Integer) is
      L : constant Big_Integer := (A - B) / M;
   begin
      --  A = B + LM, so KA = KB + KLM.
      --  Set new L' = KL, thus AK ≡ BK mod M.
      Lemma_Mod_Def (A, B, M, L);
      Lemma_Mod_Def_Helper (K*A, K*B, M, K*L);
      Lemma_Mod_Def (K*A, K*B, M, K*L);
   end Lemma_Mod_Scale_Compat;

   procedure Lemma_Mod_Composite (A, B, M, N : Big_Integer) is
      K : constant Big_Integer := (A - B) / (M * N);
   begin
      Lemma_Mod_Def (A, B, M*N, K);

      --  Using the definition of mod, once we've found a K such that
      --  A = B + MNK, we can reassociate MNK to prove the
      --  postcondition.
      Lemma_Mod_Def_Helper (A, B, M, N*K);
      Lemma_Mod_Def_Helper (A, B, N, M*K);
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
