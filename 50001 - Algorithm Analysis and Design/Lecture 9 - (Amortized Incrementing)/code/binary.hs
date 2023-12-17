data Bit = I | O

-- [LSB,...,MSB]
type Binary = [Bit]

incr :: Binary -> Binary
incr [] = [I]
incr (O:bs) = I:bs
incr (I:bs) = O:incr bs
