pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
use type Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer;

with Lemmas;

package body Ring_Buffer with SPARK_Mode => On is

   function Is_Valid (B : Buffer) return Boolean
   is (B.Read < B.Capacity
       and then B.Write < B.Capacity
       and then B.Capacity - 1 <= Natural'Last - B.Capacity);

   function Capacity_Is_Not_Too_Large (C : Capacity_Type) return Boolean
   is (C - 1 <= Natural'Last - C);

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

   function Length (B : Valid_Buffer) return Natural
   is
      R : constant Big_Integer := To_Big_Integer (B.Read);
      W : constant Big_Integer := To_Big_Integer (B.Write);
      C : constant Big_Integer := To_Big_Integer (B.Capacity);
   begin
      Lemma_Mod_Trans_Compat (To_Big_Integer (0), C, W - R, C);
      return ((B.Capacity + B.Write) - B.Read) mod B.Capacity;
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
      --  assumption, our length N ≡ W - R mod C. When N is zero, we
      --  have 0 ≡ W - R mod C, so W ≡ R mod C.
      Lemma_Mod_Trans_Compat (N, W - R, R, C);
      --  Since both 0 <= W, R < C, mod does nothing and W = R.
      Lemma_Mod_Nop (R, C);
      Lemma_Mod_Nop (W, C);

      return B.Read = B.Write;
   end Is_Empty;

   function Is_Full (B : Valid_Buffer) return Boolean
   is (Length (B) = B.Capacity);

   function Get (B : Valid_Buffer; I : Natural) return Element is
   begin
      return B.Memory (Mask (B, B.Read + I));
   end Get;

   procedure Push (B : in out Valid_Buffer; V : Element) is
   begin
      B.Memory (Mask (B, B.Write)) := V;
      B.Write := (B.Write + 1) mod B.Capacity;
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
