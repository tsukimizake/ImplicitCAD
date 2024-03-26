{-# LANGUAGE FlexibleInstances #-}
-- Implicit CAD. Copyright (C) 2011, Christopher Olah (chris@colah.ca)
-- Copyright (C) 2014 2015 2016, Julia Longtin (julial@turinglace.com)
-- Released under the GNU AGPLV3+, see LICENSE
-- FIXME: Required. why?
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

-- A module exporting all of the primitives, and some operations on them.
module Graphics.Implicit.Primitives
  ( translate,
    mirror,
    scale,
    outset,
    complement,
    union,
    intersect,
    difference,
    unionR,
    intersectR,
    differenceR,
    shell,
    getBox,
    getImplicit,
    getImplicit',
    extrude,
    extrudeM,
    link,
    extrudeOnEdgeOf,
    sphere,
    cube,
    rect3,
    circle,
    cylinder,
    cylinder2,
    cone,
    torus,
    ellipsoid,
    square,
    rect,
    polygon,
    rotateExtrude,
    rotate3,
    rotateQ,
    rotate3V,
    transform3,
    pack3,
    rotate,
    slice,
    transform,
    pack2,
    implicit,
    emptySpace,
    fullSpace,
    withRounding,
    boxFrame,
    _Shared,
    pattern Shared,
    Object (Space, canonicalize),
  )
where

import Control.Lens (Prism', preview, prism', (#))
import Data.Kind (Type)
import Graphics.Implicit.Canon (canonicalize2, canonicalize3)
import Graphics.Implicit.Definitions
  ( Box2,
    ExtrudeMScale,
    ObjectContext,
    SharedObj
      ( Complement,
        DifferenceR,
        EmbedBoxedObj,
        Empty,
        Full,
        IntersectR,
        Mirror,
        Outset,
        Scale,
        Shell,
        Translate,
        UnionR,
        WithRounding
      ),
    SymbolicObj2
      ( Circle,
        Polygon,
        Rotate2,
        Shared2,
        Slice,
        Square,
        Transform2
      ),
    SymbolicObj3
      ( BoxFrame,
        Cube,
        Cylinder,
        Ellipsoid,
        Extrude,
        ExtrudeM,
        ExtrudeOnEdgeOf,
        Link,
        Rotate3,
        RotateExtrude,
        Shared3,
        Sphere,
        Torus,
        Transform3
      ),
    defaultObjectContext,
    ℝ,
    ℝ2,
    ℝ3,
  )
import Graphics.Implicit.MathUtil (infty, pack)
import Graphics.Implicit.ObjectUtil (getBox2, getBox3, getImplicit2, getImplicit3)
import Linear (M33, M44, Quaternion, V2 (V2), V3 (V3), axisAngle)
import Prelude (Applicative, Bool (False, True), Either, Eq, Foldable, Maybe (Just, Nothing), Num, Ord, abs, fmap, max, negate, otherwise, ($), (&&), (*), (-), (.), (/), (<), (<=))

-- $ 3D Primitives

sphere ::
  -- | Radius of the sphere
  ℝ ->
  -- | Resulting sphere
  SymbolicObj3
sphere = Sphere

-- | A rectangular prism
rect3 ::
  -- | Bottom.. corner
  ℝ3 ->
  -- | Top right... corner
  ℝ3 ->
  -- | Resuting cube
  SymbolicObj3
rect3 xyz1 xyz2 = translate xyz1 $ Cube $ xyz2 - xyz1

-- | A cube
cube ::
  -- | Centered?
  Bool ->
  -- | Size
  ℝ3 ->
  -- | Resuting cube. (0,0,0) is bottom left if @center = False@,
  -- otherwise it's the center.
  SymbolicObj3
cube False size = Cube size
cube True size = translate (fmap (negate . (/ 2)) size) $ Cube size

-- | A conical frustum --- ie. a cylinder with different radii at either end.
cylinder2 ::
  -- | Radius of the cylinder
  ℝ ->
  -- | Second radius of the cylinder
  ℝ ->
  -- | Height of the cylinder
  ℝ ->
  -- | Resulting cylinder
  SymbolicObj3
cylinder2 r1 r2 h
  | h < 0 = mirror (V3 0 0 1) $ cylinder2 r1 r2 (abs h)
  | otherwise = Cylinder h r1 r2

cylinder ::
  -- | Radius of the cylinder
  ℝ ->
  -- | Height of the cylinder
  ℝ ->
  -- | Resulting cylinder
  SymbolicObj3
cylinder r = cylinder2 r r

boxFrame :: ℝ3 -> ℝ -> SymbolicObj3
boxFrame = BoxFrame

link :: ℝ -> ℝ -> ℝ -> SymbolicObj3
link = Link

cone ::
  -- | Radius of the cylinder
  ℝ ->
  -- | Height of the cylinder
  ℝ ->
  -- | Resulting cylinder
  SymbolicObj3
cone = cylinder2 0

torus :: ℝ -> ℝ -> SymbolicObj3 -- Major radius, minor radius
torus = Torus

ellipsoid :: ℝ -> ℝ -> ℝ -> SymbolicObj3 -- a, b, c
ellipsoid = Ellipsoid

-- $ 2D Primitives

circle ::
  -- | radius of the circle
  ℝ ->
  -- | resulting circle
  SymbolicObj2
circle = Circle

-- | A rectangle
rect ::
  -- | Bottom left corner
  ℝ2 ->
  -- | Top right corner
  ℝ2 ->
  -- | Resulting square
  SymbolicObj2
rect xy1 xy2 = translate xy1 $ Square $ xy2 - xy1

-- | A square
square ::
  -- | Centered?
  Bool ->
  -- | Size
  ℝ2 ->
  -- | Resulting square (bottom right = (0,0) )
  SymbolicObj2
square False size = Square size
square True size = translate (fmap (negate . (/ 2)) size) $ Square size

-- | A 2D polygon
polygon ::
  -- | Verticies of the polygon
  [ℝ2] ->
  -- | Resulting polygon
  SymbolicObj2
polygon = Polygon

-- $ Shared Operations

-- | Operations available on both 2D and 3D objects. The obvious omission of
-- rotation operations from this class are a technical limitation, and are
-- instead provided by 'rotate' and 'rotate3'.
--
-- Library users shouldn't need to provide new instances of this class.
class
  ( Applicative f,
    Eq a,
    Eq (f a),
    Foldable f,
    Ord a,
    Num a,
    Num (f a)
  ) =>
  Object obj f a
    | obj -> f a
  where
  -- | Type representing a space this object belongs to.
  -- V3 for 3D objects, V2 for 2D
  type Space obj :: Type -> Type

  -- | A 'Prism'' for including 'SharedObj's in @obj@. Prefer using 'Shared'
  -- instead of this.
  _Shared :: Prism' obj (SharedObj obj f a)

  -- | Get the bounding box an object
  getBox ::
    -- | Object to get box of
    obj ->
    -- | Bounding box
    (f a, f a)

  -- | Get the implicit function for an object
  getImplicit' ::
    ObjectContext ->
    -- | Object to get implicit function of
    obj ->
    -- | Implicit function
    (f a -> a)

  -- | Canonicalization function used to rewrite / normalize
  -- abstract syntax tree representing an object
  canonicalize :: obj -> obj

  implicit ::
    -- | Implicit function
    (f a -> a) ->
    -- | Bounding box
    (f a, f a) ->
    -- | Resulting object
    obj

{-# INLINEABLE getImplicit #-}

-- | Get the implicit function for an object
getImplicit ::
  (Object obj f a) =>
  -- | Object to get implicit function of
  obj ->
  -- | Implicit function
  (f a -> a)
getImplicit = getImplicit' defaultObjectContext

-- | A pattern that abstracts over 'Shared2' and 'Shared3'.
pattern Shared :: (Object obj f a) => SharedObj obj f a -> obj
pattern Shared v <- (preview _Shared -> Just v)
  where
    Shared v = _Shared # v

-- | Translate an object by a vector of appropriate dimension.
translate ::
  (Object obj f a) =>
  -- | Vector to translate by
  f a ->
  -- | Object to translate
  obj ->
  -- | Resulting object
  obj
translate v s = Shared $ Translate v s

-- | Scale an object
scale ::
  (Object obj f a) =>
  -- | Amount to scale by
  f a ->
  -- | Object to scale
  obj ->
  -- | Resulting scaled object
  obj
scale v s = Shared $ Scale v s

-- | Complement an Object
complement ::
  (Object obj f a) =>
  -- | Object to complement
  obj ->
  -- | Result
  obj
complement (Shared Empty) = Shared Full
complement (Shared Full) = Shared Empty
complement (Shared (Complement s)) = s
complement s = Shared $ Complement s

-- | The object that fills no space
emptySpace :: (Object obj f a) => obj
emptySpace = Shared Empty

-- | The object that fills the entire space
fullSpace :: (Object obj f a) => obj
fullSpace = Shared Full

-- | Set the current object-rounding value for the given object. The rounding
-- value is measured in units of distance, and describes the radius of rounded
-- corners.
--
-- This can be used to change the shape of more primitive forms, for example,
-- we can make a cube with rounded corners via @withRounding 5 ('cube' True
-- 20)@.
--
-- @'withRounding' r obj@ applies the rounding @r@ /all/ primitives objects in
-- @obj@, so long as they have the same dimensionality. That is to say,
-- the current object-rounding value set in 3D will not apply to extruded 2D
-- shapes.
withRounding :: (Object obj f a) => ℝ -> obj -> obj
withRounding r = Shared . WithRounding r

-- | Mirror an object across the hyperplane whose normal is a given
-- vector.
mirror ::
  (Object obj f a) =>
  -- | Vector defining the hyperplane
  f a ->
  -- | Object to mirror
  obj ->
  -- | Resulting object
  obj
mirror v s = Shared $ Mirror v s

-- | Outset of an object.
outset ::
  (Object obj f a) =>
  -- | distance to outset
  ℝ ->
  -- | object to outset
  obj ->
  -- | resulting object
  obj
outset v s = Shared $ Outset v s

-- | Make a shell of an object.
shell ::
  (Object obj f a) =>
  -- | width of shell
  ℝ ->
  -- | object to take shell of
  obj ->
  -- | resulting shell
  obj
shell v s = Shared $ Shell v s

-- | Rounded union
unionR ::
  (Object obj f a) =>
  -- | The radius (in mm) of rounding
  ℝ ->
  -- | objects to union
  [obj] ->
  -- | Resulting object
  obj
unionR r ss = Shared $ UnionR r ss

-- | Rounded difference
differenceR ::
  (Object obj f a) =>
  -- | The radius (in mm) of rounding
  ℝ ->
  -- | Base object
  obj ->
  -- | Objects to subtract from the base
  [obj] ->
  -- | Resulting object
  obj
differenceR r s ss = Shared $ DifferenceR r s ss
{-# INLINEABLE differenceR #-}

-- | Rounded minimum
intersectR ::
  (Object obj f a) =>
  -- | The radius (in mm) of rounding
  ℝ ->
  -- | Objects to intersect
  [obj] ->
  -- | Resulting object
  obj
intersectR r ss = Shared $ IntersectR r ss

instance Object SymbolicObj2 V2 ℝ where
  type Space SymbolicObj2 = V2
  _Shared = prism' Shared2 $ \case
    Shared2 x -> Just x
    _ -> Nothing
  getBox = getBox2 . canonicalize
  getImplicit' ctx = getImplicit2 ctx . canonicalize
  canonicalize = canonicalize2

  implicit a b =
    Shared $
      EmbedBoxedObj
        ( \p -> max (a p) (if pointInBox b p then -infty else 1),
          b
        )
    where
      pointInBox (V2 lx ly, V2 ux uy) (V2 x y) =
        lx <= x
          && x <= ux
          && ly <= y
          && y <= uy

instance Object SymbolicObj3 V3 ℝ where
  type Space SymbolicObj3 = V3
  _Shared = prism' Shared3 $ \case
    Shared3 x -> Just x
    _ -> Nothing
  getBox = getBox3 . canonicalize
  getImplicit' ctx = getImplicit3 ctx . canonicalize
  canonicalize = canonicalize3

  implicit a b =
    Shared $
      EmbedBoxedObj
        ( \p -> max (a p) (if pointInBox b p then -infty else 1),
          b
        )
    where
      pointInBox (V3 lx ly lz, V3 ux uy uz) (V3 x y z) =
        lx <= x
          && x <= ux
          && ly <= y
          && y <= uy
          && lz <= z
          && z <= uz

union :: (Object obj f a) => [obj] -> obj
union = unionR 0

difference :: (Object obj f a) => obj -> [obj] -> obj
difference = differenceR 0

intersect :: (Object obj f a) => [obj] -> obj
intersect = intersectR 0

-- 3D operations

-- | Extrude a 2d object upwards. The current object-rounding value set by
-- 'withRounding' is used to round the caps, but is not used by the 2D object.
extrude ::
  -- | Extrusion height
  ℝ ->
  SymbolicObj2 ->
  SymbolicObj3
extrude = Extrude

-- | The current object-rounding value set by 'withRounding' is used to round
-- the caps, but is not used by the 2D object.
extrudeM ::
  -- | twist
  Either ℝ (ℝ -> ℝ) ->
  -- | scale
  ExtrudeMScale ->
  -- | translate
  Either ℝ2 (ℝ -> ℝ2) ->
  -- | object to extrude
  SymbolicObj2 ->
  -- | height to extrude to
  Either ℝ (ℝ2 -> ℝ) ->
  SymbolicObj3
extrudeM = ExtrudeM

rotateExtrude ::
  -- | Angle to sweep to (in rad)
  ℝ ->
  -- | translate
  Either ℝ2 (ℝ -> ℝ2) ->
  -- | rotate
  Either ℝ (ℝ -> ℝ) ->
  -- | object to extrude
  SymbolicObj2 ->
  SymbolicObj3
rotateExtrude = RotateExtrude

extrudeOnEdgeOf :: SymbolicObj2 -> SymbolicObj2 -> SymbolicObj3
extrudeOnEdgeOf = ExtrudeOnEdgeOf

-- | Rotate a 3D object via an Euler angle, measured in radians, along the
-- world axis.
rotate3 :: ℝ3 -> SymbolicObj3 -> SymbolicObj3
rotate3 (V3 pitch roll yaw) =
  Rotate3 $
    axisAngle (V3 0 0 1) yaw
      * axisAngle (V3 0 1 0) roll
      * axisAngle (V3 1 0 0) pitch

rotateQ ::
  Quaternion ℝ ->
  SymbolicObj3 ->
  SymbolicObj3
rotateQ = Rotate3

-- | Rotate a 3D object along an arbitrary axis.
rotate3V ::
  -- | Angle of rotation
  ℝ ->
  -- | Axis of rotation
  ℝ3 ->
  SymbolicObj3 ->
  SymbolicObj3
rotate3V w xyz = Rotate3 $ axisAngle xyz w

-- | Transform a 3D object using a 4x4 matrix representing affine transformation
-- (OpenSCAD multmatrix)
transform3 ::
  M44 ℝ ->
  SymbolicObj3 ->
  SymbolicObj3
transform3 = Transform3

-- | Attempt to pack multiple 3D objects into a fixed area. The @z@ coordinate
-- of each object is dropped, and the resulting packed objects will all be on
-- the same plane.
--
-- FIXME: shouldn't this pack into a 3d area, or have a 3d equivalent?
pack3 ::
  -- | Area to pack
  ℝ2 ->
  -- | Separation between objects
  ℝ ->
  -- | Objects to pack
  [SymbolicObj3] ->
  -- | 'Just' if the objects could be packed into the given area
  Maybe SymbolicObj3
pack3 (V2 dx dy) sep objs =
  let boxDropZ :: (ℝ3, ℝ3) -> (ℝ2, ℝ2)
      boxDropZ (V3 a b _, V3 d e _) = (V2 a b, V2 d e)
      withBoxes :: [(Box2, SymbolicObj3)]
      withBoxes = fmap (\obj -> (boxDropZ $ getBox3 obj, obj)) objs
   in case pack (V2 0 0, V2 dx dy) sep withBoxes of
        (a, []) -> Just $ union $ fmap (\(V2 x y, obj) -> translate (V3 x y 0) obj) a
        _ -> Nothing

-- 2D operations

rotate :: ℝ -> SymbolicObj2 -> SymbolicObj2
rotate = Rotate2

-- | Transform a 2D object using a 3x3 matrix representing affine transformation
-- (OpenSCAD multmatrix)
transform ::
  M33 ℝ ->
  SymbolicObj2 ->
  SymbolicObj2
transform = Transform2

-- | Attempt to pack multiple 2D objects into a fixed area.
pack2 ::
  -- | Area to pack
  ℝ2 ->
  -- | Separation between objects
  ℝ ->
  -- | Objects to pack
  [SymbolicObj2] ->
  -- | 'Just' if the objects could be packed into the given area
  Maybe SymbolicObj2
pack2 (V2 dx dy) sep objs =
  let withBoxes :: [(Box2, SymbolicObj2)]
      withBoxes = fmap (\obj -> (getBox2 obj, obj)) objs
   in case pack (V2 0 0, V2 dx dy) sep withBoxes of
        (a, []) -> Just $ union $ fmap (\(V2 x y, obj) -> translate (V2 x y) obj) a
        _ -> Nothing

-- 3D to 2D
-- Slice 3D object by intersecting it with a XY plane to produce 2D outline
slice ::
  SymbolicObj3 ->
  SymbolicObj2
slice = Slice
