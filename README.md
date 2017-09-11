hgmp
====

Haskell interface to GMP.  Types and instances, and marshalling between Integer
and Rational and the corresponding GMP types, along with raw foreign imports of
GMP functions.  Allows FFI to GMP code (whether in GMP itself or in third-party
code that uses GMP).

A simple example illustrating binding to GMP's next probable-prime function:

    {-# LANGUAGE ForeignFunctionInterface #-}

    import Foreign.Ptr (Ptr(..))
    import Numeric.GMP.Types (MPZ)
    import Numeric.GMP.Utils (withInInteger, withOutInteger_)
    import Numeric.GMP.Raw.Safe (mpz_nextprime)
    import System.IO.Unsafe (unsafePerformIO)

    nextPrime :: Integer -> Integer
    nextPrime n =
      unsafePerformIO $
        withOutInteger_ $ \rop ->
          withInInteger n $ \op ->
            mpz_nextprime rop op
