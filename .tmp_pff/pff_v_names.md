17:- :  : Nat.Even 0.
20:- :  : ~ Nat.Even 1.
27:- :  : ~ Nat.Odd 0.
30:- :  : Nat.Odd 1.
123:- :  :
133:- :  : forall p : positive, nat_of_P p <> 0.
142:- :  :
156:- :  :
174:- :  : forall x y : nat, (Z_of_nat x <= Z_of_nat y)%Z -> x <= y.
181:- :  : forall x y : Z, (x < y)%Z -> (- y < - x)%Z.
187:- :  : forall x y : Z, (x <= y)%Z -> (- y <= - x)%Z.
191:- :  : forall z : Z, Z.abs z = Z_of_nat (Z.abs_nat z).
196:- :  : forall z : Z, Zpower_nat z 0 = Z_of_nat 1.
200:- :  : forall z : Z, Zpower_nat z 1 = z.
204:- :  :
211:- :  : forall z : Z, (- Z.pred z)%Z = Z.succ (- z).
223:- :  : forall z1 z2 : Z, (z1 <= Zmax z1 z2)%Z.
230:- :  : forall z1 z2 : Z, Zmax z1 z2 = Zmax z2 z1.
242:- :  : forall z1 z2 : Z, (z2 <= Zmax z1 z2)%Z.
246:- :  :
252:- :  : forall z1 z2 : Z, (Z.min z1 z2 <= Zmax z1 z2)%Z.
258:- :  :
266:- :  :
274:- :  :
284:- :  :
289:- :  :
295:- :  :
302:- :  : forall p : Z, (p <= Z_of_nat (Z.abs_nat p))%Z.
309:- :  : forall n m : nat, (Z_of_nat n < Z_of_nat m)%Z -> n < m.
318:- :  : forall p : positive, nat_of_P p <> 0.
326:- :  : forall z : Z, z <> 0%Z -> 0 < Z.abs_nat z.
331:- :  : forall r : R, (0 <= r)%R -> (r <= 2 * r)%R.
337:- :  : forall r : R, (0 < r)%R -> (r < 2 * r)%R.
344:- :  : forall x y : R, (0 < x)%R -> (x <= y)%R -> (/ y <= / x)%R.
352:- :  : forall x, (x <= 0)%Z -> Z.abs x = (- x)%Z.
357:- :  : forall z : Z, (Z.abs (Z.succ z) <= Z.succ (Z.abs z))%Z.
364:- :  : forall x y : Z, (x < y)%Z -> (x <= Z.pred y)%Z.
369:- :  : forall z : Z, Z.abs (- z) = Z.abs z.
373:- :  : forall z : Z, (z <= Z.abs z)%Z.
380:- :  :
390:- :  :
402:- :  :
408:- :  :
416:- :  :
424:- :  :
431:- :  :
439:- :  :
445:- :  : forall z : Z, Z.pred (- z) = (- Z.succ z)%Z.
449:- :  : forall z : Z, (1 <= z)%Z -> (0 < z)%Z.
453:- :  : forall p q : Z, (q < p)%Z -> p <> q.
457:- :  :
462:- :  :
467:- :  :
474:- :  :
498:- :  : forall q : nat, (0 < Zpower_nat n q)%Z.
503:- :  :
513:- :  :
522:- :  :
531:- :  :
572:- :  :
579:- :  :
591:- :  :
615:- :  :
637:- :  :
668:- :  :
681:- :  : forall q : Z, (Z.abs q < Zpower_nat n (digit q))%Z.
697:- :  :
722:- :  :
740:- :  : forall q : Z, q <> 0%Z -> 0 < digit q.
750:- :  :
772:- :  : forall p : Z, digit (Z.abs p) = digit p.
777:- :  :
804:- :  : forall (e : R) (n : nat), e <> 0%R -> (e ^ n)%R <> 0%R.
808:- :  :
815:- :  :
823:- :  : forall (e : R) (n : nat), (0 < e)%R -> (0 < e ^ n)%R.
829:- :  :
844:- :  :
865:- :  :
899:- :  :
905:- :  :
924:- :  : forall e : R, powerRZ e 0 = 1%R.
928:- :  : forall e : R, powerRZ e (Z.succ 0) = e.
932:- :  : forall (e : R) (z : Z), e <> 0%R -> powerRZ e z <> 0%R.
937:- :  :
987:- :  :
995:- :  :
1007:- :  :
1020:- :  : forall (e : R) (z : Z), (0 < e)%R -> (0 < powerRZ e z)%R.
1025:- :  :
1031:- :  :
1049:- :  :
1059:- :  : forall n : Z, powerRZ 1 n = 1%R.
1069:- :  :
1081:- :  :
1091:- :  :
1101:- :  :
1136:- :  :
1142:- :  : forall x y : float, {x = y} + {x <> y}.
1162:- :  : forall z : Z, Fzero z = 0%R :>R.
1166:- :  : forall x : float, is_Fzero x -> x = 0%R :>R.
1171:- :  : forall x : float, (0 < Fnum x)%Z -> (0 < x)%R.
1179:- :  : forall x : float, x = 0%R :>R -> is_Fzero x.
1189:- :  :
1198:- :  :
1205:- :  :
1212:- :  :
1221:- :  :
1230:- :  :
1242:- :  :
1251:- :  :
1259:- :  :
1270:- :  : forall p q : float, p = q :>R -> Fexp p = Fexp q -> p = q.
1284:- :  :
1291:- :  : forall (n : nat) (x : float), Fshift n x = x :>R.
1301:- :  :
1312:- :  : forall x : float, Fshift 0 x = x.
1318:- :  :
1332:- :  :
1387:- :  :
1399:- :  :
1408:- :  :
1417:- :  : forall p : float, (0 < p)%R -> (0 < Fnum p)%Z.
1425:- :  : forall p : float, (0 <= p)%R -> (0 <= Fnum p)%Z.
1433:- :  : forall x : float, (0 <= Fnum x)%Z -> (0 <= x)%R.
1440:- :  : forall p : float, (p < 0)%R -> (Fnum p < 0)%Z.
1448:- :  : forall p : float, (p <= 0)%R -> (Fnum p <= 0)%Z.
1456:- :  : forall x : float, (Fnum x <= 0)%Z -> (x <= 0)%R.
1489:- :  : forall x y : float, Fplus x y = (x + y)%R :>R.
1506:- :  : forall x : float, Fopp x = (- x)%R :>R.
1512:- :  : forall p : float, Fopp (Fopp p) = p.
1517:- :  : forall x : float, Fdigit radix (Fopp x) = Fdigit radix x.
1526:- :  :
1546:- :  :
1567:- :  : forall x : float, Fabs x = Rabs x :>R.
1576:- :  :
1593:- :  : forall x : float, ~ is_Fzero x -> ~ is_Fzero (Fabs x).
1600:- :  : forall x : float, Fdigit radix (Fabs x) = Fdigit radix x.
1607:- :  : forall x y : float, Fminus x y = (x - y)%R :>R.
1613:- :  : forall p q : float, Fopp (Fminus p q) = Fminus q p.
1620:- :  :
1670:- :  : forall b : Fbound, Fzero (- dExp b) = 0%R :>R.
1674:- :  : forall b : Fbound, Fbounded b (Fzero (- dExp b)).
1681:- :  :
1687:- :  :
1695:- :  :
1704:- :  :
1712:- :  :
1719:- :  :
1726:- :  :
1766:- :  :
1779:- :  :
1799:- :  :
1830:- :  :
1838:- :  :
1888:- :  :
1935:- :  :
1975:- :  :
1988:- :  :
1996:- :  :
2015:- :  :
2026:- :  :
2036:- :  :
2057:- :  :
2070:- :  :
2083:- :  :
2096:- :  :
2126:- :  : forall p : float, Fnormal p -> Fbounded b p.
2131:- :  : forall p : float, Fnormal p -> ~ is_Fzero p.
2137:- :  : forall p : float, Fnormal p -> Fnormal (Fopp p).
2146:- :  : forall p : float, Fnormal p -> Fnormal (Fabs p).
2158:- :  :
2188:- :  : forall p : float, Fsubnormal p -> Fbounded b p.
2192:- :  :
2199:- :  : forall p : float, Fsubnormal p -> Fsubnormal (Fopp p).
2205:- :  : forall p : float, Fsubnormal p -> Fsubnormal (Fabs p).
2215:- :  :
2222:- :  :
2236:- :  : forall p : float, Fcanonic p -> Fbounded b p.
2241:- :  : forall p : float, Fcanonic p -> Fcanonic (Fopp p).
2247:- :  : forall p : float, Fcanonic p -> Fcanonic (Fabs p).
2256:- :  :
2271:- :  :
2307:- :  :
2316:- :  :
2327:- :  :
2336:- :  :
2346:- :  :
2352:- :  :
2371:- :  :
2389:- :  :
2409:- :  :
2419:- :  :
2462:- :  : (0 < nNormMin)%Z.
2467:- :  : digit radix nNormMin = precision.
2474:- :  : (nNormMin <= Zpos (vNum b))%Z.
2483:- :  : Fnormal firstNormalPos.
2499:- :  :
2512:- :  :
2537:- :  :
2553:- :  :
2570:- :  :
2583:- :  :
2597:- :  :
2606:- :  :
2630:- :  : forall p : float, Fnormalize p = p :>R.
2639:- :  :
2652:- :  :
2675:- :  :
2747:- :  :
2763:- :  :
2772:- :  :
2793:- :  :
2820:- :  :
2838:- :  :
2857:- :  :
2866:- :  :
2881:- :  :
2896:- :  : (1 < Zpos (vNum b))%Z.
2902:- :  : Zpos (vNum b) = (radix * nNormMin)%Z.
2909:- :  :
2928:- :  :
2934:- :  :
2946:- :  :
2990:- :  :
3000:- :  :
3023:- :  :
3047:- :  :
3063:- :  :
3094:- :  :
3108:- :  :
3133:- :  : (nNormMin radix precision < Zpos (vNum b))%Z.
3139:- :  :
3185:- :  :
3232:- :  :
3270:- :  : forall f : float, Fbounded b f -> Fbounded b (FSucc f).
3295:- :  :
3305:- :  :
3313:- :  :
3377:- :  :
3418:- :  :
3428:- :  :
3436:- :  : forall a : float, (a < FSucc a)%R.
3481:- :  :
3577:- :  : forall x : float, (x < 0)%R -> (FSucc x <= 0)%R.
3607:- :  :
3697:- :  :
3705:- :  :
3821:- :  :
3828:- :  : forall a : float, (a < FNSucc a)%R.
3835:- :  :
3862:- :  : (nNormMin radix precision < pPred (vNum b))%Z.
3918:- :  :
3928:- :  :
3950:- :  :
3975:- :  :
3991:- :  :
4021:- :  :
4036:- :  :
4048:- :  :
4061:- :  : forall f : float, Fbounded b f -> Fbounded b (FPred f).
4067:- :  :
4076:- :  : forall a : float, (FPred a < a)%R.
4085:- :  : forall x : float, (0 < x)%R -> (0 <= FPred x)%R.
4095:- :  :
4112:- :  :
4119:- :  :
4126:- :  : forall a : float, (FNPred a < a)%R.
4134:- :  :
4217:- :  :
4324:- :  : forall n : nat, (n < boundNat n)%R.
4338:- :  : forall r : R, (r < boundR r)%R.
4355:- :  : forall r : R, boundR r = boundR (- r).
4360:- :  : forall r : R, (Fopp (boundR r) < r)%R.
4383:- :  :
4429:- :  : forall r : R, In (Fopp (boundR r)) (mBFloat r).
4452:- :  :
4475:- :  :
4540:- :  : forall (p : float) (r : R), isMin r p -> (p <= r)%R.
4544:- :  : ProjectorP isMin.
4553:- :  : MonotoneP isMin.
4571:- :  : forall (p : float) (r : R), isMax r p -> (r <= p)%R.
4575:- :  : ProjectorP isMax.
4584:- :  : MonotoneP isMax.
4595:- :  :
4609:- :  :
4623:- :  :
4642:- :  :
4662:- :  :
4695:- :  :
4737:- :  : forall r : R, exists min : float, isMin r min.
4777:- :  : forall r : R, exists max : float, isMax r max.
4789:- :  :
4843:- :  :
4860:- :  :
4907:- :  : forall n : Z, Odd n -> Even (Z.succ n).
4912:- :  : forall n : Z, Even n -> Odd (Z.succ n).
4918:- :  : forall n : Z, Odd (Z.succ n) -> Even n.
4923:- :  : forall n : Z, Even (Z.succ n) -> Odd n.
4928:- :  : Even 0.
4933:- :  : Odd 1.
4938:- :  : forall z : Z, Odd z -> Odd (- z).
4943:- :  : forall z : Z, Even z -> Even (- z).
4948:- :  : forall n : Z, {Odd n} + {Even n}.
4967:- :  : forall n : Z, Odd n -> ~ Even n.
4978:- :  : forall n : Z, Even n -> ~ Odd n.
4989:- :  : forall n m : Z, Even n -> Even m -> Even (n + m).
4994:- :  : forall n m : Z, Even n -> Odd m -> Odd (n + m).
5001:- :  : forall n m : Z, Even n -> Even (n * m).
5005:- :  : forall n m : Z, Even m -> Even (n * m).
5010:- :  : forall n m : Z, Odd n -> Odd m -> Odd (n * m).
5017:- :  : forall n m : Z, Even (n * m) -> Odd n -> Even m.
5023:- :  :
5033:- :  :
5048:- :  : forall p : float, Feven p \/ Fodd p.
5052:- :  :
5113:- :  :
5118:- :  :
5123:- :  : forall p : float, Feven p -> Feven (Fopp p).
5133:- :  :
5149:- :  :
5165:- :  : forall p : float, FNeven p -> FNeven (Fopp p).
5172:- :  :
5183:- :  :
5194:- :  : forall p : float, FNeven p \/ FNodd p.
5198:- :  : forall n : float, FNodd n -> ~ FNeven n.
5240:- :  : forall P, RoundedModeP P -> CompatibleP P.
5244:- :  : forall P, RoundedModeP P -> MonotoneP radix P.
5249:- :  : forall P, RoundedModeP P -> ProjectorP b radix P.
5259:- :  : CompatibleP (isMin b radix).
5265:- :  : RoundedModeP (isMin b radix).
5272:- :  : CompatibleP (isMax b radix).
5278:- :  : RoundedModeP (isMax b radix).
5285:- :  : UniqueP (isMin b radix).
5291:- :  : UniqueP (isMax b radix).
5298:- :  :
5307:- :  :
5397:- :  :
5619:- :  : forall z, oZ1 z = Z_of_nat (oZ z).
5626:- :  :
5693:- :  :
5716:- :  :
5734:- :  :
5741:- :  :
5751:- :  :
5762:- :  :
5795:- :  : forall m : Z, Zdivides m 1.
5799:- :  :
5819:- :  :
5864:- :  : forall (v : Z) (p : nat), maxDiv v p <= p.
5869:- :  :
5880:- :  :
5890:- :  :
5903:- :  :
5911:- :  :
5926:- :  :
5934:- :  :
5947:- :  :
5959:- :  :
5972:- :  :
5988:- :  :
6020:- :  :
6028:- :  :
6039:- :  :
6051:- :  : forall x : float, LSB x = LSB (Fopp x).
6057:- :  :
6076:- :  : forall x : float, LSB x = LSB (Fabs x).
6084:- :  :
6091:- :  :
6102:- :  : forall x : float, MSB x = MSB (Fopp x).
6107:- :  : forall x : float, MSB x = MSB (Fabs x).
6112:- :  : forall x : float, ~ is_Fzero x -> (LSB x <= MSB x)%Z.
6120:- :  : forall x : float, (Fexp x <= LSB x)%Z.
6125:- :  :
6131:- :  :
6151:- :  :
6172:- :  :
6180:- :  :
6197:- :  :
6226:- :  :
6271:- :  :
6289:- :  :
6300:- :  :
6307:- :  :
6343:- :  :
6362:- :  :
6376:- :  :
6399:- :  :
6413:- :  :
6437:- :  :
6451:- :  :
6467:- :  :
6479:- :  :
6486:- :  :
6494:- :  : forall f : float, Fulp f = Fulp (Fabs f) :>R.
6506:- :  :
6560:- :  :
6584:- :  :
6595:- :  :
6605:- :  :
6619:- :  :
6646:- :  :
6672:- :  :
6690:- :  :
6701:- :  :
6719:- :  :
6730:- :  :
6852:- :  :
6915:- :  :
6940:- :  :
6968:- :  :
6988:- :  :
7008:- :  :
7026:- :  :
7044:- :  :
7065:- :  :
7090:- :  :
7144:- :  :
7257:- :  :
7461:- :  :
7532:- :  :
7551:- :  :
7612:- :  :
7644:- :  :
7718:- :  :
7798:- :  :
7942:- :  : TotalP Closest.
8014:- :  : CompatibleP b radix Closest.
8023:- :  :
8074:- :  :
8122:- :  : MinOrMaxP b radix Closest.
8171:- :  :
8206:- :  :
8241:- :  : MonotoneP radix Closest.
8360:- :  : RoundedModeP b radix Closest.
8371:- :  : TotalP EvenClosest.
8447:- :  : CompatibleP b radix EvenClosest.
8464:- :  : MinOrMaxP b radix EvenClosest.
8469:- :  : MonotoneP radix EvenClosest.
8474:- :  : RoundedModeP b radix EvenClosest.
8484:- :  : UniqueP radix EvenClosest.
8534:- :  : SymmetricP Closest.
8554:- :  : SymmetricP EvenClosest.
8597:- :  :
8614:- :  :
8647:- :  :
8703:- :  :
8719:- :  :
8745:- :  :
8761:- :  :
8804:- :  :
8825:- :  :
8878:- :  :
8899:- :  :
8922:- :  :
8993:- :  :
9058:- :  :
9309:- :  :
9348:- :  :
9358:- :  :
9368:- :  :
9415:- :  :
9430:- :  :
9512:- :  :
9537:- :  :
9593:- :  :
9635:- :  :
9707:- :  :
9952:- :  :
10003:- :  :
10028:- :  :
10047:- :  :
10065:- :  :
10109:- :  :
10169:- :  :
10190:- :  :
10213:- :  :
10277:- :  :
10380:- :  :
10402:- :  :
10423:- :  : (0 < pPred (vNum b))%Z.
10429:- :  : (radix < pPred (vNum b))%Z.
10439:- :  :
10498:- :  :
10507:- :  :
10579:- :  :
10616:- :  :
10682:- :  :
10721:- :  :
10748:- :  :
10813:- :  :
10880:- :  :
11111:- :  :
11197:- :  :
11294:- :  :
11338:- :  :
11580:- :  :
11618:- :  :
11676:- :  :
11886:- :  :
12165:- :  :
12302:- :  :
12464:- :  :
12484:- :  :
12523:- : : (Fcanonic radix b f)
12601:- : : (Rabs(z-f) <= (powerRZ radix e)/2)%R
12698:- : : (Rabs(z-f) < (powerRZ radix e)/2)%R
12789:- : : (Rabs(z-f) < (powerRZ radix e)/2)%R
12816:- : : (EvenClosest b radix p z f) ->
12890:- : : (Even radix)%Z
12990:- : : Zpos (vNum b')=(Zpower_nat radix (minus t s)).
13016:- : : (0 <= p)%R.
13024:- : : (q <= 0)%R.
13038:- : :  forall (f : float) (z : R),
13056:- : : (FtoRradix hx=p+q)%R.
13167:- : : (Fexp q <= Fexp p)%Z.
13184:- : : (Fexp p <=s+1+Fexp x)%Z.
13222:- : : (Fexp q <= s+ Fexp x)%Z \/
13549:- : : (s+ Fexp x <= Fexp q)%Z.
13763:- : : (Fexp q=s+Fexp x)%Z \/
13772:- : : forall v:float,  (FtoRradix v=hx) -> Fcanonic radix b' v ->
14024:- : :
14190:- : : (Even radix)
14486:- : : (Odd radix)
14711:- : : forall x p q hx:float,
14790:- : : forall x p q hx:float,
14834:- : : forall x p q hx:float,
14858:- : : forall x p q hx:float,
14944:- : : forall x p q hx:float,
15002:- : : forall x p q hx:float,
15053:- : : forall f:float,
15108:- : : forall b0:Fbound, forall z:R, forall f:float,
15124:- : : forall b0:Fbound, forall n:nat, forall fext f:float,
15289:- : : forall b0:Fbound, forall n:nat, forall fext f:float,
15368:- : : forall b0:Fbound, forall n:nat, forall z:R, forall f1 f2:float,
15453:- : : forall b0:Fbound, forall n:nat, forall fext f:float,
15562:- : : forall x p q hx:float,
15737:- : : forall x p q hx:float,
15890:- : : forall x p q hx:float,
15947:- : : forall x p q hx:float,
16003:- : : forall x p q hx tx:float,
16083:- : : forall x p q hx tx:float,
16158:- : : forall x p q hx tx:float,
16271:- : : forall x p q hx tx:float,
16330:- : : forall (r:R) (x:float) (e:Z),
16367:- : : forall (r:R) (x:float),
16381:- : : forall bext:Fbound, forall fext f:float,
16559:- : : forall (a' a:float),
16615:- : : forall (r:R) (x1:float),
16752:- : : forall (r:R) (x1:float),
16777:- : : forall (x x' y y' z' z:float) (rx ry epsx epsy:R),
16901:- : : forall (x x' y y' z' z:float) (rx ry epsx epsy:R),
16984:- : : (Rabs (x2*y2) <= (powerRZ radix (2*s+Fexp x+Fexp y)) /4)%R.
16994:- : : (Rabs (x2*y1) < (powerRZ radix (t+s+Fexp x+Fexp y)) /2
17023:- : : (Rabs (x1*y2) < (powerRZ radix (t+s+Fexp x+Fexp y)) /2
17051:- : : (Rabs e <= (powerRZ radix (t+Fexp x+Fexp y)) /2)%R.
17111:- : : (t - 1 + Fexp x + Fexp y <= Fexp r)%Z.
17163:- : : forall (e1 e2:Z),
17179:- : : (exists x':float, (FtoRradix x'=r-x1*y1)%R /\ (Fbounded b x')
17250:- : : (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2)%R /\ (Fbounded b x')
17291:- : : (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2-x2*y1)%R /\ (Fbounded b x')
17331:- : : (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2-x2*y1-x2*y2)%R /\ (Fbounded b x')).
17343:- : : (exists x':float, (FtoRradix x'=r-x1*y1-x1*y2-x2*y1-x2*y2)%R /\ (Fbounded b x')
17364:- : : Zpos (vNum bt)=(Zpower_nat radix s).
17393:- : : (exists x':float, (FtoRradix x'=x1*y1)%R /\ (Fbounded b x')
17417:- : : (exists x':float, (FtoRradix x'=x1*y1)%R /\ (Fbounded b x')).
17422:- : : (exists x':float, (FtoRradix x'=x1*y2)%R /\ (Fbounded b x')
17444:- : : (exists x':float, (FtoRradix x'=x1*y2)%R /\ (Fbounded b x')).
17450:- : : (exists x':float, (FtoRradix x'=x2*y1)%R /\ (Fbounded b x')
17471:- : : (exists x':float, (FtoRradix x'=x2*y1)%R /\ (Fbounded b x')).
17529:- : : (2 <= s).
17543:- : : (s <= t-2).
17560:- : : (t <= s + s)%Z.
17574:- : : (s + s <= t + 1)%Z.
17592:- : : (exists x':float, (FtoRradix x'=tx*ty)%R /\ (Fbounded b x'))
17710:- : : (radix=2)%Z \/ (Nat.Even t) ->
17820:- : : (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
17881:- : : (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
18134:- : : (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
18387:- : : (radix=2)%Z \/ (Nat.Even t) ->  (x*y=r-t4)%R.
18423:- : : forall (f pf qf hf tf:float),
18492:- : : (dExp b < dExp b')%Z.
18503:- : : (Z_of_N (N.double (dExp b) + Npos (xO (P_of_succ_nat t)))
18515:- : : forall (f:float), Fcanonic radix b f -> (FtoRradix f <>0) ->
18574:- : :
18824:- : :
18986:- : : (radix=2)%Z \/ (Nat.Even t) ->
19080:- : : (delta <= (/2)*(Fulp bo radix precision d)+
19107:- : : (Rle 0 p)%R.
19113:- : : forall x y:float, (0 <= x)%R ->
19133:- : : forall x y:float, (0 <= x)%R ->
19155:- : : forall (x:float) (r:R),
19179:- : : forall (x:float) (r:R),
19309:- : : forall (p q : R) (p' q' : float),
19324:- : : forall (x y:float) (r:R), (0 <= x)%R ->
19350:- : : (delta <= 2*(Fulp bo radix precision d))%R.
19521:- : : (0 < q)%R.
19534:- : : (q <= 2*p)%R.
19554:- : : (p <= 2*q)%R.
19573:- : : (FtoRradix t=p-q)%R.
19585:- : : (Rabs (dp-dq) <= (3/2)*(Rmin
19614:- :  :
19637:- : : (3*(Rmin (Fulp bo radix precision p) (Fulp bo radix precision q))
19705:- : : (exists f:float, (Fbounded bo f) /\ (FtoRradix f)=(dp-dq)%R)
19731:- : :
19822:- : : (Fexp p)=(Fexp q) -> (delta <= 2*(Fulp bo radix precision d))%R.
19959:- : : (0 < dp*dq)%R -> (delta <= 2*(Fulp bo radix precision d))%R.
20054:- : : (0< dp)%R -> (dq < 0)%R
20141:- : : (dp < 0)%R -> (0 < dq)%R
20293:- : : (delta <= 2*(Fulp bo radix precision d))%R.
20370:- : : (delta <= 2*(Fulp bo radix precision d))%R.
20638:- : : forall f:float, forall r:R,
20706:- : : (FtoRradix v=u)%R.
20717:- : : (FtoRradix d=p-q)%R.
20724:- : : (q <= p)%R -> (delta <= 2*(Fulp bo radix precision d))%R.
21391:- : : (delta <= 2*(Fulp bo radix precision d))%R.
21483:- : : forall f:float, forall r:R,
21506:- : :  (q <= p)%R -> (delta <= 2*(Fulp bo radix precision d))%R.
21901:- : : (delta <= 2*(Fulp bo radix precision d))%R.
22001:- : : (delta <= 2*(Fulp bo radix precision d))%R.
22099:- : : (delta <= 2*(Fulp bo radix precision d))%R.
22293:- : : forall e:Z, forall f:float,
22311:- : : forall f1:float ,forall f2:float, forall g:float, forall e:Z,
22341:- : : forall f1:float ,forall f2:float, forall g:float, forall e:Z,
22352:- : : forall f1:float ,forall f2:float, forall g:float, forall e:Z,
22417:- : : forall f1:float ,forall f2:float, forall g:float, forall e:Z,
22468:- : : (FtoRradix b <> 0)%R ->
22487:- : : (a*c <> 0)%R ->
22506:- : : (FtoRradix b=0)%R \/ (a*c=0)%R
22619:- : : (FtoRradix d=0)%R \/ (delta <= 2*(Fulp bo radix precision d))%R.
22936:- : : (delta <= 2*(Fulp bo radix precision d))%R.
23065:- :  :
23077:- :  :
23090:- :  :
23101:- :  :
23117:- :  :
23123:- :  :
23133:- :  :
23154:- :  :
23168:- :  :
23179:- :  :
23191:- :  :
23230:- :  :
23252:- :  :
23293:- :  :
23313:- :  :
23359:- :  :
23407:- : : (0 < Unmoins)%R.
23420:- : : forall (z : R) (f : float),
23439:- : : forall (z : R) (f : float),
23456:- : : (Rabs b <= Rabs a)%R -> (2*powerRZ radix (Fexp b) <= Rabs (a+b))%R
23478:- : : (Rabs b <= Rabs a)%R -> (powerRZ radix (Fexp b) = Rabs (a+b))%R
23523:- :  :  (Rabs b <= Rabs a)%R -> (Rabs x <= 2*Rabs y)%R.
23597:- :  : (Rabs b <= Rabs a)%R -> ~(FtoRradix x=0)%R
23710:- :  : (Rabs x <= 2*Rabs y)%R.
23719:- : : ~(FtoRradix x=0)%R -> (Rabs y <= 2*Rabs x)%R.
23729:- : : exists v:float, (FtoRradix v=x-y)%R /\ (Fbounded bo v) /\
23796:- : : forall x y:float,
23847:- : :
24209:- : :
24259:- : : forall (a b x y:float),
24297:- : : exists v:float, (FtoRradix v=be1-r1)%R /\ (Fbounded bo v)
24364:- : : (a*x+y=r1+ga+al2)%R.
24445:- :  : (Fexp r1 <= Fexp be1+1)%Z.
24482:- : : (Fexp be1 <= Fexp r1+1)%Z.
24513:- :  : forall z1 z2 z3 : Z,
24524:- : :
24621:- : : exists v:float, (FtoRradix v=be1-r1+be2)%R /\ (Fbounded bo v).
24695:- : : (a*x+y=r1+ga+al2)%R.
24770:- : : (a*x+y=r1+ga+al2)%R.
24794:- : : forall (r:R) (f g:float), (Closest bo radix r f) -> (FtoRradix f=0)%R ->
24820:- : : forall (r:R) (x:float),
24832:- : : forall f g:float, Closest bo radix f g
24858:- : : forall (n:Z) (f g:float), Closest bo radix f g
24902:- : : (a*x+y=r1+ga+al2)%R.
25043:- : : (exists ga_e:float, exists al2_e:float,
25126:- : : (0 <= z)%R.
25133:- : : (0 <= uh)%R.
25147:- : : exists v:float, Fbounded bo v /\ (FtoRradix v=uh-z)%R.
25534:- : : exists v:float, Fbounded bo v /\ (FtoRradix v=uh-z)%R.
25628:- : :
25721:- : : (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
25811:- : : forall (f:float) (r:R), (Closest bo radix r f) ->
25913:- : : (Fexp ph <= Fexp uh+1)%Z.
25922:- : : (Fexp uh <= Fexp z+1)%Z.
26018:- : :  (Fexp ph = Fexp uh+1)%Z -> (Fexp uh = Fexp z+1)%Z -> False.
26109:- : : (powerRZ radix (Fexp ph)+powerRZ radix (Fexp uh) <= 2*powerRZ radix (Fexp z+1))%R.
26120:- : : (Rabs (pl+ul) <= powerRZ radix (Fexp z)*radix)%R.
26139:- : : (Rabs v <= powerRZ radix (Fexp z)*radix)%R.
26153:- : : (Rabs t <= powerRZ radix (Fexp z)*(radix+1))%R.
26191:- : : (Rabs w <= powerRZ radix (Fexp z)*(2*radix+1))%R.
26219:- : : (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
26313:- : : (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
26492:- : : (Rabs (z+w-(a*x+b)) <= (3*radix/2+/2)*powerRZ radix (2-2*p)*Rabs z)%R.
26553:- :  :
26569:- :  :
26610:- :  :
26620:- :  :
26631:- :  :
26677:- :  :
26689:- :  :
26694:- :  :
26708:- :  :
26739:- :  :
26837:- :  :
26943:- :  :
26957:- :  :
26981:- :  :
27026:- :  :
27064:- :  : (0 < ln radix)%R.
27069:- :  : forall x y : R, (exp x <= exp y)%R -> (x <= y)%R.
27075:- :  : forall x y : R, (x <= y)%R -> (exp x <= exp y)%R.
27081:- :  :
27095:- :  : forall r : R, (IRNDD r <= r)%R.
27104:- :  : forall r : R, (r < Z.succ (IRNDD r))%R.
27110:- :  : forall r : R, (r - 1 < IRNDD r)%R.
27118:- :  : forall r : R, (0 <= r)%R -> (0 <= IRNDD r)%R.
27127:- :  :
27148:- :  : forall z : Z, IRNDD z = z.
27166:- :  :
27191:- :  :
27298:- :  : forall r : R, (0 <= r)%R -> (RND_Min_Pos r <= r)%R.
27330:- :  :
27402:- :  :
27494:- :  :
27529:- :  :
27537:- :  : forall r : R, (0 <= r)%R -> (r <= RND_Max_Pos r)%R.
27552:- :  :
27594:- :  : forall r : R, Fcanonic radix b (RND_Min r).
27602:- :  : forall r : R, isMin b radix r (RND_Min r).
27617:- :  : forall r : R, Fcanonic radix b (RND_Max r).
27625:- :  : forall r : R, isMax b radix r (RND_Max r).
27658:- :  :
27671:- :  :
