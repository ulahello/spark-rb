pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
use type Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer;

with Lemmas;

package body Ring_Buffer with SPARK_Mode => On is

   function Is_Valid (B : Buffer) return Boolean
   is (Capacity_Is_Not_Too_Large (B.Capacity)
     and then B.Read < B.Capacity + B.Capacity
     and then B.Write < B.Capacity + B.Capacity
     and then Length (B) <= B.Capacity);

   function Capacity_Is_Not_Too_Large (C : Capacity_Type) return Boolean
   is (C <= Natural'Last - C
     and then 2 * C - 1 <= Natural'Last - 2 * C);

   function Buffer_Init (Capacity : Capacity_Type) return Valid_Buffer is
      Buffer_Empty : constant Buffer :=
        (Capacity => Capacity,
         Memory   => [others => Uninit],
         Read     => 0,
         Write    => 0);
   begin
      return Buffer_Empty;
   end Buffer_Init;

   function Mask (B : Valid_Buffer; I : Natural) return Positive
   is (1 + I mod B.Capacity);

   function Length (B : Buffer) return Natural
   is
      Read : constant Integer := B.Read mod (2 * B.Capacity);
      Write : constant Integer := B.Write mod (2 * B.Capacity);
      Rs : constant Big_Integer := To_Big_Integer (B.Read);
      Ws : constant Big_Integer := To_Big_Integer (B.Write);
      R : constant Big_Integer := To_Big_Integer (Read);
      W : constant Big_Integer := To_Big_Integer (Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
   begin
      --  Note that our buffer isn't known to be valid, but we want to
      --  be working with read and write indices mod 2C, so we must
      --  show that this is equivalent.
      Lemma_Mod_Idempotent (Rs, 2 * C);
      Lemma_Mod_Idempotent (Ws, 2 * C);
      --  With unbounded indices W*, R*, and W, R both defined mod 2C,
      --  we show W* - R* ≡ W - R mod 2C.
      --  (First, W* - R* ≡ W - R* mod 2C)
      Lemma_Mod_Trans_Compat (Ws, W, -Rs, 2*C);
      --  (Next, W - R* ≡ W - R mod 2C)
      Lemma_Mod_Trans_Compat (-Rs, -R, W, 2*C);
      Lemma_Mod_Scale_Compat (Rs, R, -1, 2*C);
      --  Computing length, we add 2C to avoid overflow.
      Lemma_Mod_Trans_Compat (To_Big_Integer (0), 2 * C, W - R, 2 * C);
      return ((2 * B.Capacity + Write) - Read) mod (2 * B.Capacity);
   end Length;

   function Is_Empty (B : Valid_Buffer) return Boolean is
      N : constant Big_Integer := To_Big_Integer (Length (B));
      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
   begin
      --  This direction is trivial
      pragma Assert (if B.Read = B.Write then Length (B) = 0);

      --  The other requires some modular arithmetic lemmas. By
      --  assumption, our length N ≡ W - R mod 2C. When N is zero, we
      --  have 0 ≡ W - R mod 2C, so W ≡ R mod 2C.
      Lemma_Mod_Trans_Compat (N, W - R, R, 2*C);
      --  Since both 0 <= W, R < 2C, mod does nothing and W = R.
      Lemma_Mod_Nop (R, 2*C);
      Lemma_Mod_Nop (W, 2*C);

      return B.Read = B.Write;
   end Is_Empty;

   function Is_Full (B : Valid_Buffer) return Boolean
   is (Length (B) = B.Capacity);

   function Get (B : Valid_Buffer; I : Natural) return Element is
   begin
      return B.Memory (Mask (B, B.Read + I));
   end Get;

   procedure Push (B : in out Valid_Buffer; V : Element) is
      N : constant Big_Integer := To_Big_Integer (Length (B));
      Np : Big_Integer;
      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
   begin

      --  FIXME: while writing this realized there's an error with how
      --  i'm defining capacity, the buffer can never be full because
      --  length is mod C. also this is incomplete.

      pragma Assert (N < C);
      pragma Assert (N = (W - R) mod C);

      B.Memory (Mask (B, B.Write)) := V;
      B.Write := (B.Write + 1) mod B.Capacity;

      Np := To_Big_Integer (Length (B));
      pragma Assert (Np = ((W + 1) mod C - R) mod C);
      Lemma_Mod_Sum_Simp (-R, W + 1, C);
      pragma Assert (Np = (W - R + 1) mod C);
      Lemma_Mod_Trans_Compat (Np, W - R + 1, -1, C);
      Lemma_Mod_Nop (N, C);
      Lemma_Mod_Nop (Np, C);
      pragma Assert ((Np - 1) mod C = (W - R) mod C);
      pragma Assert (N mod C = (Np - 1) mod C);
      Lemma_Mod_Trans_Compat (N, Np - 1, 1, C);
      pragma Assert ((N + 1) mod C = Np mod C);
      Lemma_Mod_Nop (N + 1, C);
   end Push;

   procedure Pop (B : in out Valid_Buffer; V : out Element) is
   begin
      V := B.Memory (Mask (B, B.Read));
      B.Read := (B.Read + 1) mod B.Capacity;
   end Pop;

   procedure Clear (B : in out Valid_Buffer) is
   begin
      B.Write := B.Read;
   end Clear;

   procedure Truncate_Back (B : in out Valid_Buffer; To_Length : Natural) is
   begin
      if To_Length < Length (B) then
         B.Read := (B.Write - To_Length) mod B.Capacity;
      end if;
   end Truncate_Back;

end Ring_Buffer;
