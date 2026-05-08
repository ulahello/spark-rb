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

   procedure Lemma_Mod_Sum_Simp (A, B, M : Big_Integer) is
   begin
      Lemma_Mod_Idempotent (B, M);
      --  pragma Assert ((A mod M) + (B mod M) = (A + B) mod M);
      pragma Assume ((A + B mod M) mod M = (A + B) mod M, "sorry");
   end Lemma_Mod_Sum_Simp;

   procedure Lemma_Mod_Nop (N, M : Big_Integer) is null;

   procedure Lemma_Mod_Trans_Compat (A, B, K, M : Big_Integer) is
   begin
      pragma Assume ((if A mod M = B mod M then (A + K) mod M = (B + K) mod M), "sorry");
   end Lemma_Mod_Trans_Compat;

   procedure Lemma_Mod_Scale_Compat (A, B, K, M : Big_Integer) is
   begin
      pragma Assume ((if A mod M = B mod M then (A * K) mod M = (B * K) mod M), "sorry");
   end Lemma_Mod_Scale_Compat;

end Lemmas;
