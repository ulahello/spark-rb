pragma Ada_2022;

with Ada.Numerics.Big_Numbers.Big_Integers;
use Ada.Numerics.Big_Numbers.Big_Integers;
use type Ada.Numerics.Big_Numbers.Big_Integers.Big_Integer;

with Lemmas; use Lemmas;

generic
   type Element is private;
   Uninit : Element;
package Ring_Buffer
with
  SPARK_Mode => On
is

   subtype Capacity_Type is Natural
   with Dynamic_Predicate => Is_Power_Of_Two (Capacity_Type);

   type Element_Array is array (Positive range <>) of Element;

   type Buffer (Capacity : Capacity_Type) is record
      Memory : Element_Array (1 .. Capacity);
      Read   : Natural;
      Write  : Natural;
   end record;

   function Capacity_Is_Not_Too_Large (C : Capacity_Type) return Boolean
     with Ghost,
          Post => Capacity_Is_Not_Too_Large'Result
                  = (C - 1 <= Natural'Last - C);

   function Is_Valid (B : Buffer) return Boolean
     with Post => Is_Valid'Result =
                    (B.Read < B.Capacity
                     and then B.Write < B.Capacity
                     and then Capacity_Is_Not_Too_Large (B.Capacity));

   subtype Valid_Buffer is Buffer
     with Dynamic_Predicate => Is_Valid (Valid_Buffer);

   function Buffer_Init (Capacity : Capacity_Type) return Valid_Buffer
     with Pre => Capacity_Is_Not_Too_Large (Capacity),
          Post => Buffer_Init'Result.Capacity = Capacity
                  and then Is_Empty (Buffer_Init'Result);

   --  Translating indices

   function Mask (B : Valid_Buffer; I : Natural) return Positive
     with Post => Mask'Result <= B.Capacity and Mask'Result = 1 + I mod B.Capacity;

   --  Buffer operations

   function Length (B : Valid_Buffer) return Natural
   with Post => Length'Result in 0 .. B.Capacity
     and then To_Big_Integer (Length'Result) = (To_Big_Integer (B.Write) - To_Big_Integer (B.Read)) mod To_Big_Integer (B.Capacity);

   function Is_Empty (B : Valid_Buffer) return Boolean
   with Post => Is_Empty'Result = (B.Read = B.Write)
      and then (Length (B) = 0) = (B.Read = B.Write);

   function Is_Full (B : Valid_Buffer) return Boolean
   with Post => Is_Full'Result = (Length (B) = B.Capacity);

   function Get (B : Valid_Buffer; I : Natural) return Element
   with Pre => I <= Length (B),
        Post => Get'Result = B.Memory (Mask (B, B.Read + I));

   procedure Push (B : in out Valid_Buffer; V : Element)
     with Pre => not Is_Full (B),
          Post => Length (B'Old) + 1 = Length (B)
                  and then (for all I in 0 .. Length (B'Old) - 1
                             => Get (B'Old, I) = Get (B, I))
                  and then Get (B, Length (B'Old)) = V;

   procedure Pop (B : in out Valid_Buffer; V : out Element)
     with Pre => not Is_Empty (B),
          Post => Length (B) + 1 = Length (B'Old)
                  and then (for all I in 1 .. Length (B)
                             => Get (B'Old, I) = Get (B, I - 1))
                  and then Get (B'Old, 0) = V;

   procedure Clear (B : in out Valid_Buffer)
   with Post => Is_Empty (B);

   procedure Truncate_Back (B : in out Valid_Buffer; To_Length : Natural)
     with Post => Length (B) = Natural'Min (To_Length, Length (B'Old))
                  and then (for all I in 0 .. Length (B)
                             => Get (B'Old, I + (Length (B) - Length (B'Old)))
                                = Get (B, I));

end Ring_Buffer;
