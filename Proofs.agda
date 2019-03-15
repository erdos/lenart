{-
Geometriai tételek bizonyítása típuselméleti eszközökkel

Az alábbiakban gömbi geometriai axiomákból levezethető tételeket fogunk bizonyítani típuselméleti eszközökkel.
Létrehozzuk a geometria elemeit reprezentáló típusokat, majd a megfelelően formalizált tételekre konstruktív
módon bizonyításokat fogunk adni.
-}

module Beadando where

open import Function
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_)
open import Data.Nat

open import Data.List

{- Pontok halmaza -}
data ℙ : Set where

{-

Amikor a gömb geometriájával foglalkozunk, általában első lépésben egységsugarú gömböt veszünk fel. Ez megkönnyíti
a számolást és a mérést, ugyanis ekkor két pont távolsága, amelyet radián szögben adunk meg, megegyezik a felszínen
lemért távolsággal. Ezzel szemben a bonyolultabb számolások után a kapott eredményeket normalizálni kell, vagyis
visszavetíteni az egységgömbünkre.

Legyen ℙ = {(x,y,z) : ℝ³, x²+y²+z² = 1} a gömbfelszín pontjai. Ekkor egy P pont köré szerkeszthető gömbi főkör pontjai az <P,X>=0 egyenlet megoldásai ℙ-ben.

Most a gömbi geometriából származtatható projektív geometriával foglalkozunk, amelyet megkaphatunk, ha a gömbi geometriánk
szemközti pontjait egymásnak megfeleltetjük. Az egyszerűség kedvéért kiléphetünk az egységsugarú gömb felszínéről.
Definiáljunk egy ekvivalenciarelációt, amely akkor és csak akkor áll fenn két nemnulla térpont között, ha létezik
nemnulla valós szám, amellyel megszorozva az egyik a másikba vihető. Az ekvivalenciaosztályok legyenek a geometriánk
új pontjai.

-}

data _perp_ : ℙ → ℙ → Set where
  comm'' : ∀ {a b} → (a perp b) → (b perp a)

{-

Lénárt István aximarendszerét fogjuk vizsgálni. [1] Adott a fent definiált pontok felett értélmezett művelet, amelyet a szövegben ~ jellel fogunk jelölni. Olvasd: BANG vagy BUMM. Ez a művelet olyan, hogy teljesül rá az alábbi két axioma:
 - Kommutativitás: ( a ~ b ) ≡ ( b ~ a )
 - Főaxioma: ( a ~ b ) ~ ( a ~ c ) ≡ a

A művelet lényegében a vektorokként értelmezett alapidomaink feletti vektoriális szorzat. Ez alapján kifejezhető a merőlegességi relációval is, úgymint:
-}

data _bang'_is_ : ℙ → ℙ → ℙ → Set where
  perps : ∀ {a b c} → ( a perp c ) → ( b perp c ) → ( a bang' b is c )

comm' : ∀ {a b c} → (a bang' b is c) → (b bang' a is c)
comm' ( perps a b ) = ( perps b a )

main' : ∀ {a b c ab ac} → ( (a bang' b is ab) × (a bang' c is ac) ) → ( ab bang' ac is a )
main' ( perps x y , perps v w ) = perps ( comm'' x ) ( comm'' v )

{-
Amely a merőlegességi reláció ismerete nélkül még igen kevés. Definiáljuk a műveletet inkább háromváltozós relációként az ismert axiomákat felhasználva:
-}

data _bang_is_ : ℙ → ℙ → ℙ → Set where
  comm : ∀ {a b c} → ( a bang b is c ) → (b bang a is c)
  main : ∀ {a b c ab ac} → ( (a bang b is ab) × (a bang c is ac) ) → ( ab bang ac is a )

{-barmely ket ponthoz van kulonbozo harmadik.-}
postulate
  ex₁ : ∀ {a : ℙ} → ∃ λ x → ( a ≢ x )
  ex₂ : ∀ {a b : ℙ} → ∃ λ x → ( a ≢ x ) × ( a ≢ x)
  ex₃ : ∀ {a b c : ℙ} → ∃ λ x → ( a ≢ x ) × ( b ≢ x) × ( c ≢ x)

 -- exx : ∀ {a : List ℙ } → ∃ λ x → ∑

infix 5 _bang_is_

{-
Itt (A bang B is C) azt reprezentálja, hogy  (A ~ B = C). Ezzel a relációval kiváltottuk alapidom típusa és az alapművelet definícióját.
KÉRDÉS: Miért kell, hogy set1-be képezzünk?
-}

{-
A fenti azonban teljesen használhatatlannak tűnik, mivel nem lehet megmondani, hogy pontosan mik az elemei a relációnak, illetve a reláció operandusai is titkosak. A lenti két hasznos művelet megvalósíthatatlannak tűnik.
-}

{-postulate
  result : ∀ {a b c : ℙ} → (a bang b is c) → c
  operands : ∀ {a b c : ℙ} → (a bang b is c) → (a × b)
-}

{-
A művelet-reláció-típusunk mégis elég bizonyos tételek bizonyításához.
-}

{-
Theorem 1
banged by itself

Tétel: a~a definiálatlan

Bizonyítás: Legyen a, b különböző, ekkor a~b=x és b~a=x. Nézzük meg, hogy mi lesz x~x eredménye. Az axiomák miatt a és b is lehet, ami ellentmondás, mert a művelet egyértelmű hozzárendelés, és feltettük, hogy a és b különböző.

-}

postulate
  x-bang-y : ∀ {a b} → ∃ λ ab → (a bang b is ab)

-- A bizonyításhoz szükségünk van arra, hogy több, különböző pont is létezik.
postulate
  2diffpoints : ∀ { a : Set } → ∃ λ b → (a ≢ b)


-- foaxioma forditva.
lemma_t1 : ∀ {a b c ab ac} → ( (b bang a is ab) × (c bang a is ac) ) → ( ab bang ac is a )
lemma_t1 (f , g) = main (comm f , comm g)

theorem1 : ∀ {a b} → ¬ (a bang a is b)
--theorem1 x = main ( a-bang-b , a-bang-b ) == main (comm a-bang-b , comm a-bang-b)
theorem1 = {!!}


{-
Theorem 2
symmetrization - szimmetrizáció

Tétel: Ha a~b=a~c, akkor a~b=a~c=b~c.

Bizonyítás: Tfh a, b, c különböző. Indirekt tfh. a~b=a~c es a~c/=b~c. Ekkor ac/=bc. De x~x definiálatlan. Tehát, ha ab/=bc, akkor felírhatjuk, hogy ab=ac esetén (ab)(bc)=(ac)(bc), ahonnan a főaxioma miatt b=c, de feltettük, hogy a, b, c különböző.

-}

theorem2 : ∀ {a b c x} → ( (a bang b is x) × (a bang c is x) ) → (b bang c is x)
theorem2 ( f , g ) = main (main (comm f , comm f) , main (comm g , comm g))


{-
Theorem 3
symmetrization of four

Tétel: Ha a~b=c~d, akkor ab=cd=ac=bd=ad=bc.

Bizonyítás: Mint a fentire, de négy elemmel.

-}

lemma_t3 : ∀ {a b c d x} → ( (a bang b is x) × (c bang d is x) ) → (a bang c is x)
lemma_t3 (f , g) = main (main (f , f) , main (g , g))

theorem3 : ∀ {a b c d x} →  ( (a bang b is x) × (c bang d is x) ) → ( (a bang c is x) × (a bang d is x) × (b bang c is x) × (b bang d is x) )
theorem3 ( f , g) = ( lemma_t3 (f , g ) ,  lemma_t3 (f , comm g ) ,  lemma_t3 ( comm f , g ) ,  lemma_t3 ( comm f , comm g ))


{-
A második tételt a harmadik felhasználásával finomíthatjuk.
-}

theorem2b : ∀ {a b c x} → ( (a bang b is x) × (a bang c is x) ) → (b bang c is x)
theorem2b (f , g) = lemma_t3 ( comm f , comm g)


{-
Theorem 4
Triangle inequality

Tétel: Ha ab/=ac akkor ab/=ac/=bc.

Bizonyítás: ez a második tétel egyszerű következménye. [sic!] Ha ab=ac miatt ab=ac=bc, akkor ab/=bc miatt ab, ac, bc különböző.

-}

theorem4 : ∀ {a b c ab ac bc} → ( (a bang b is ab) × (a bang c is ac) × (b bang c is bc) × (ab ≢ ac)) → ( (ab ≢ bc) × (bc ≢ ac) )
theorem4 = {!!}


{-
Theorem 5
[octahedron]

Itt van egy hiba a forrásban, a pontos tétel itt található.
Tétel: Ha ab=c, bc=a, akkor ca=b.

Bizonyítás: Következik, hogy (ab)(bc)=ca, de (ab)(bc)=b, teház ac=b.

-}

theorem5 : ∀ {a b c} → ( (a bang b is c) × (b bang c is a) ) → (c bang a is b)
theorem5 ( f , g ) = main ( comm f ,  g )


{-
Theorem 6
associativity - asszociativitás.
Ez a tétel tisztázatlan, hiszen belátható, hogy az operátorunk általában nem asszociatív. Ez szemben áll a forrás levezetésével.
-}

associativity : ∀ {a b c ab bc abc1 abc2} →  ¬ ( (a bang b is ab) × (b bang c is bc) × (ab bang c is abc1) × (a bang bc is abc2) → (abc1 ≡ abc2) )
associativity f = {!!}

-- Egyéb tulajdonságok.

-- Cancellation IS FALSE
cancellation : ∀ {a b c x} → ¬ ( ( (a bang b is x) × (a bang c is x) ) → (b ≡ c) )
cancellation f = {!!}

{-
  Property: General Unit Element
  Általános egységelem
  Van-e olyan elem, ami bármely x elemmel x-et eredményezi?
  Ez azt jelentené, hogy x merőleges önmagára, ami nem állhat fenn.
-}

general_unit : ∄ λ e → ∀ {x} → (x bang e is x)
general_unit e = {!!}


-- Spherical Unit element XXX
spherical_unit : ∄ λ e → ∀ {x} → (x bang e is e)
spherical_unit e = general_unit ({!!} , {!!})

-- Inverse operation - Does not exist.

-- Perpendiculars in sets of three elements

-- question often asked by students

-- orthocenter


{-

[1] Lénárt István, Spherical Algebra ( https://docs.google.com/viewer?a=v&q=cache:UNt-49cS9ekJ:www.crcnetbase.com/doi/abs/10.1201/b10670-19+&hl=hu&gl=hu&pid=bl&srcid=ADGEESg6fTdFyxySaFYyirbZaR-8T40MhNg5Uw1n_sDfpxabmsoZ--yW5qLfeWqkG6a6tsUT76mN62wL-qSYZ-rwa2QpOuFjB2sBuNNWjlA5WfDBwDEM1OiN_vncaqofxV2taBm2W4-F&sig=AHIEtbS9CQr8F3NSbOPXDWHAcg27Vu3ShQ )

- Agda: http://wiki.portal.chalmers.se/agda/agda.php?n=Main.QuickGuideToEditingTypeCheckingAndCompilingAgdaCode

- Mathematical Wizardry for a Gardner https://epdf.tips/mathematical-wizardry-for-a-gardner3e53fce3b45818ffb33dc2b32df3c08668016.html

-}
