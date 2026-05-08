pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
use type Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer;

package Lemmas with SPARK_Mode => On is

   --  Ring buffer capacity is a power of two, we formally define this.

   function Is_Power_Of_Two (N : Natural) return Boolean
     with Post => Is_Power_Of_Two'Result =
                  (case N is
                     when 0 => False,
                     when 1 => True,
                     when others => N mod 2 = 0
                                    and then Is_Power_Of_Two (N / 2)),
          Subprogram_Variant => (Decreases => N);

   procedure Lemma_Exp2_Implies_Power2 (K, N : Natural)
     with Ghost,
          Pre => To_Big_Integer (2) ** K = To_Big_Integer (N),
          Post => Is_Power_Of_Two (N),
          Subprogram_Variant => (Decreases => K,
                                 Decreases => N);

   --  TODO: Lemma_Power2_Implies_Exp2

   --  Useful properties of modular arithmetic. See
   --  https://en.wikipedia.org/wiki/Modular_arithmetic#Basic_properties.

   procedure Lemma_Mod_Idempotent (N, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (N mod M) = (N mod M) mod M;

   procedure Lemma_Mod_Sum_Simp (A, B, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (A + B mod M) mod M = (A + B) mod M;

   procedure Lemma_Mod_Nop (N, M : Big_Integer)
     with Ghost,
          Pre => 0 <= N and then N < M,
          Post => (N mod M) = N;

   procedure Lemma_Mod_Trans_Compat (A, B, K, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (if A mod M = B mod M
                   then (A + K) mod M = (B + K) mod M);

end Lemmas;
