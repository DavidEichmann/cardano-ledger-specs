{-# LANGUAGE EmptyDataDecls        #-}

module Main where
import Criterion.Main
import System.IO (isEOF)

import NonIntegral

import qualified Data.Fixed as FP

data E34

instance FP.HasResolution E34 where
    resolution _ = 10000000000000000000000000000000000

type Digits34 = FP.Fixed E34

type FixedPoint = Digits34

precision :: FixedPoint
precision = 10000000000000000000000000000000000

epsilon :: FixedPoint
epsilon = 100000000000000000

doTestsFromStdin = do
  b <- isEOF
  if b then return ()
    else do
    line <- getLine
    let base     = read (takeWhile (/= ' ') line)        :: FixedPoint
    let exponent = read (tail $ dropWhile (/= ' ') line) :: FixedPoint
    putStrLn $ show ((base / precision) *** (exponent / precision))
            ++ " " ++ show (exp' (base / precision))
    main

main :: IO ()
main = defaultMain [
  bgroup "***" [
   bench "1" $ whnf ((***) 13.2537787738760641755376502809034752) 45.9650132023219801122678173987766272,
   bench "1" $ whnf ((***) 21.9959186212478939576566810908033024) 67.9864716740685320723722320893444096,
   bench "1" $ whnf ((***) 93.5692896226738780239819442090934272) 52.0416372022747454755038068918452224,
   bench "1" $ whnf ((***) 3.5572110464847438658621000753610752) 53.0700193141057148796603927067885568,
   bench "1" $ whnf ((***) 0.8698186061599178016839257995345920) 6.7842237262567550912485920681754624,
   bench "1" $ whnf ((***) 68.7772712409045218677237524992098304) 93.1436494969692729683863493865897984,
   bench "1" $ whnf ((***) 52.7928777759906053349458218592501760) 65.4918962180522563964940116488617984,
   bench "1" $ whnf ((***) 70.2190594499176628519353723293532160) 76.3198039998634025568863980865191936,
   bench "1" $ whnf ((***) 4.8464513386311943174129704947941376) 32.9234226160007695845405254423150592,
   bench "1" $ whnf ((***) 75.7410486132585916475077118859935744) 36.6338670891576770364321402200260608,
   bench "1" $ whnf ((***) 98.3550286321034279316900414304026624) 75.4355835205582835881179333959614464,
   bench "1" $ whnf ((***) 7.3685882820231065878204334016036864) 88.5707128815841388784728276161527808,
   bench "1" $ whnf ((***) 43.7411405515639515926670748791341056) 47.8731765118408124102889574557024256,
   bench "1" $ whnf ((***) 27.5906840076478324717730408223997952) 16.7507200194652839689498413431259136,
   bench "1" $ whnf ((***) 89.8656286732214356920544015218114560) 6.1564327533513653582490711808278528,
   bench "1" $ whnf ((***) 50.5522894934610842134489594628931584) 32.0032941085453044152882062648410112,
   bench "1" $ whnf ((***) 49.4976685206683080322997356437962752) 9.1732894580629795064426413072318464,
   bench "1" $ whnf ((***) 7.4749075222416952086275606162964480) 38.5142147968053562835285961001140224,
   bench "1" $ whnf ((***) 91.4817442071026505531811954721554432) 46.5445824948437078206920528205185024,
   bench "1" $ whnf ((***) 5.1083983708707576175800161188970496) 77.1204547001944331932077135063154688,
   bench "1" $ whnf ((***) 12.6365375577727370437324925436952576) 68.9455301054184269138551670428401664,
   bench "1" $ whnf ((***) 63.0543418124007866926297675984797696) 72.6411998660791682802467003426668544,
   bench "1" $ whnf ((***) 88.9572214067262526845885219646472192) 30.7321830882615579596165570289991680,
   bench "1" $ whnf ((***) 51.4273702178878126522261227247239168) 84.6981560313644065403306525232988160,
   bench "1" $ whnf ((***) 84.2510639570235198523653107629424640) 41.6394615428571792155199886898233344,
   bench "1" $ whnf ((***) 46.8917368501955056412849664233046016) 17.9327703682644204038452725428518912,
   bench "1" $ whnf ((***) 57.2654810708495527940453948329033728) 3.4053754301980716094514512284090368,
   bench "1" $ whnf ((***) 49.9480119058587559718046117430034432) 74.9292651237894527529873173079130112,
   bench "1" $ whnf ((***) 89.1737481571761229349640790133964800) 84.3039612731397230566496953287311360,
   bench "1" $ whnf ((***) 21.3751514550890100882157511395770368) 13.1427261803096352444070168075698176
               ]
  ]
