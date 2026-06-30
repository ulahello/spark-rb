pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;

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

   --  Useful properties of modular arithmetic. See
   --  https://en.wikipedia.org/wiki/Modular_arithmetic#Basic_properties.

   procedure Lemma_Mod_Negate (N, M: Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (-N) mod (-M) = -(N mod M);

   procedure Lemma_Mod_Diff_Def (A, B, M, K : Big_Integer)
     with Ghost,
          Pre => M /= 0 and then K = (A - B) / M,
          Post => (A = B + K*M) = ((A - B) mod M = 0);

   procedure Lemma_Mod_Diff_Divides (A, B, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (A mod M = B mod M) = ((A - B) mod M = 0);

   procedure Lemma_Mod_Def (A, B, M, K : Big_Integer)
     with Ghost,
          Pre => M /= 0 and then K = (A - B)/M,
          Post => (A mod M = B mod M) = (A = B + K*M);

   procedure Lemma_Mod_Def_Helper (A, B, M, K : Big_Integer)
     with Ghost,
          Pre => M /= 0 and then A = B + K*M,
          Post => K = (A - B)/M;

   procedure Lemma_Mod_Idempotent (N, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (N mod M) = (N mod M) mod M;

   procedure Lemma_Mod_Nop (N, M : Big_Integer)
     with Ghost,
          Pre => 0 <= N and then N < M,
          Post => (N mod M) = N;

   procedure Lemma_Mod_Add_Simp (A, B, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (A + B mod M) mod M = (A + B) mod M;

   procedure Lemma_Mod_Mul_Simp (A, B, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (A * (B mod M)) mod M = (A * B) mod M;

   procedure Lemma_Mod_Trans_Compat (A, B, K, M : Big_Integer)
     with Ghost,
          Pre => M /= 0,
          Post => (if A mod M = B mod M
                   then (A + K) mod M = (B + K) mod M);

   procedure Lemma_Mod_Scale_Compat (A, B, K, M : Big_Integer)
     with Ghost,
          Pre => M /= 0 and then A mod M = B mod M,
          Post => (A * K) mod M = (B * K) mod M;

   procedure Lemma_Mod_Composite (A, B, M, N : Big_Integer)
     with Ghost,
          Pre => M /= 0 and then N /= 0
                 and then A mod (M*N) = B mod (M*N),
          Post => (A mod M = B mod M)
                   and then (A mod N = B mod N);

   --  Ring buffer specific

   procedure Lemma_Push_Increases_Length (R, W, C, N, Np, dW : Big_Integer)
     with Ghost,
          Pre => (0 < C)
                  and then (0 <= N + dW and then N + dW <= C)
                  and then N = (W - R) mod (C*2)
                  and then Np = ((W + dW) mod (2*C) - R) mod (2*C),
          Post => N + dW = Np;

   procedure Lemma_Pop_Decreases_Length (R, W, C, N, Np, dR : Big_Integer)
     with Ghost,
          Pre => (0 < C)
                  and then (0 <= N - dR and then N - dR <= C)
                  and then N = (W - R) mod (C*2)
                  and then Np = (W - (R + dR) mod (2*C)) mod (2*C),
          Post => N = Np + dR;

   procedure Lemma_Pop_Shifts_Back_Elements (R, Rp, C, I, dR : Big_Integer)
     with Ghost,
          Pre => (0 <= R and then R < 2 * C)
                  and then Rp = (R + dR) mod (2*C),
          Post => (Rp + I) mod C = (R + I + dR) mod C;

end Lemmas;
