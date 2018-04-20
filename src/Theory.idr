-- Functor.idr ---

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

module ClaimedFunctor

import Control.Monad.Identity

%default total

interface Functor f => ClaimedFunctor (f: Type -> Type) where
  identity : (x : f a) -> map Prelude.Basics.id x = x
  distributivity : (x : f a) -> (g : a -> b) -> (h : b -> c) -> map (h . g) x = map h (map g x)

interface (ClaimedFunctor m, Monad m) => ClaimedMonad (m : Type -> Type) where
  pure_bind : (x : a) -> (f : a -> m a) -> Prelude.Applicative.pure x >>= f = f x
  bind_pure : (x : m a) -> x >>= Prelude.Applicative.pure = x
  associativity : (x : m (m (m a))) -> Prelude.Monad.join (Prelude.Monad.join x) = Prelude.Monad.join (map Prelude.Monad.join x)
  neutral : (ma : m a) -> Prelude.Monad.join (map Prelude.Applicative.pure ma) = Prelude.Monad.join (Prelude.Applicative.pure ma)


ClaimedFunctor Identity where
  identity (Id x)           = Refl

  distributivity (Id _) _ _ = Refl

ClaimedMonad Identity where
  pure_bind _ _              = Refl

  bind_pure (Id _)           = Refl

  associativity (Id _)       = Refl

  neutral (Id _)             = Refl

ClaimedFunctor Maybe where
  identity (Just _)           = Refl
  identity Nothing            = Refl

  distributivity (Just _) _ _ = Refl
  distributivity Nothing _ _  = Refl

ClaimedMonad Maybe where
  pure_bind _ _                = Refl

  bind_pure (Just _)           = Refl
  bind_pure Nothing            = Refl

  associativity (Just (Just (Just _))) = Refl
  associativity (Just (Just Nothing))  = Refl
  associativity (Just Nothing)         = Refl
  associativity Nothing                = Refl

  neutral (Just _) = Refl
  neutral Nothing = Refl

ClaimedFunctor (Either a) where
  identity (Left _)            = Refl
  identity (Right _)           = Refl

  distributivity (Left _) _ _  = Refl
  distributivity (Right _) _ _ = Refl

ClaimedFunctor List where
  identity []                  = Refl
  identity (_ :: xs)           = rewrite identity xs in Refl

  distributivity [] _ _        = Refl
  distributivity (_ :: xs) g h = rewrite distributivity xs g h in Refl

ClaimedMonad List where
  pure_bind a f                 = appendNilRightNeutral (f a)

  bind_pure []                  = Refl
  bind_pure (_ :: xs)           = rewrite bind_pure xs in Refl

  associativity []              = Refl
  associativity (xs :: xss)     = ?list_assoc

  neutral []                    = Refl
  neutral xs                    = ?list_neutral

