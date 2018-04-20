-- Isomorphism.idr ---

-- Copyright (C) 2018 Hussein Ait-Lahcen

-- Author: Hussein Ait-Lahcen <hussein.aitlahcen@gmail.com>

-- This program is free software; you can redistribute it and/or
-- modify it under the terms of the GNU General Public License
-- as published by the Free Software Foundation; either version 3
-- of the License, or (at your option) any later version.

-- This program is distributed in the hope that it will be useful,
-- but WITHOUT ANY WARRANTY; without even the implied warranty of
-- MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
-- GNU General Public License for more details.

-- You should have received a copy of the GNU General Public License
-- along with this program. If not, see <http://www.gnu.org/licenses/>.

module Isomorphism

import Control.Isomorphism
import Data.String

%default total

data B = Zero | One
data T = TT Bool
data U = UU B

isoTU : Iso T U
isoTU = MkIso f g gf fg
where
  f : T -> U
  f (TT True)  = UU One
  f (TT False) = UU Zero

  g : U -> T
  g (UU One)  = TT True
  g (UU Zero) = TT False

  fg : (t : T) -> g (f t) = t
  fg (TT x) with (g (f (TT x)))
    fg (TT x) | (TT x) = Refl

  gf : (u : U) -> f (g u) = u
  gf (UU One) with (f (g (UU One)))
    gf (UU One) | (UU x) = Refl
  gf (UU Zero) with (f (g (UU Zero)))
    gf (UU Zero) | (UU x) = Refl

x : T
x = TT False

y : U
y = let (MkIso f g a b) = isoTU in f x

main : IO ()
main = case y of
  (UU Zero) => putStrLn "Dude ZERO"
  (UU One)  => putStrLn "Dude ONE"
