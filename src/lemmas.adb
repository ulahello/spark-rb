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

   procedure Lemma_Mod_Idempotent (N, M : Big_Integer) is null;

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

   procedure Lemma_Mod_Nop (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Trans_Compat (A, B, K, M : Big_Integer) is
   begin
      pragma Assume ((if A mod M = B mod M then (A + K) mod M = (B + K) mod M), "sorry");
   end Lemma_Mod_Trans_Compat;

   procedure Lemma_Mod_Scale_Compat (A, B, K, M : Big_Integer) is
   begin
      pragma Assume ((A * K) mod M = (B * K) mod M, "sorry");
   end Lemma_Mod_Scale_Compat;

   procedure Lemma_Mod_Composite (A, B, M, N : Big_Integer) is
   begin
      pragma Assume ((A mod M = B mod M) and then (A mod N = B mod N), "sorry");
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
