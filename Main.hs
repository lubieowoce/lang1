module Main where

import Compiler (
    Expr (..), Op1 (..), Op2 (..),
    Stmt (..),
    eNot, eAdd, eMul, eSub, eEqual, eLess, eGreater, eLessEqual, eGreaterEqual,
    Definition (..),
    compileProgram, evalCompile
    )
import VM

import Data.Map (Map)
import qualified Data.Map as M

import Data.List (intersperse, nub)
import Data.Maybe (catMaybes)

import Control.Monad (forM_)

-- ################
-- #     Main     #
-- ################


prettyShowVM :: VM -> String
prettyShowVM (VM {frames=[]}) =  "<no stack frames>"
prettyShowVM vm@(VM {frames = frames}) =
    prettyShowVMStack . reverse $ frames

prettyShowVMStack :: [VMFrame] -> String
prettyShowVMStack [frame] = unlines $ prettyShowVMFrame frame
prettyShowVMStack (VMFrame {instructionPointer=ip, instructions=ops} : innerFrames) = 
    "-------\n" ++ op' ++ "\n-------\n" ++ (indent . prettyShowVMStack $ innerFrames) ++ "-------\n...\n"
    where
        indent = unlines. map ("    "++) . lines
        op' = (show ip) ++ "  " ++ (show $ ops !! ip)



prettyShowVMFrame :: VMFrame -> [String]
prettyShowVMFrame VMFrame {instructionPointer=ip, instructions=ops, stack=stack, vars=vars} =
    [separate "|" vars' stack', "-------"] ++ ops'
    where
        vars' = (joinWith " " vars)
        stack' = joinWith " " $ reverse stack
        ops' = catMaybes . map (\i -> showOp i <$> (ops !? i)) $ [ip, ip+1, ip+2]
        showOp i op = (show i) ++ "  " ++ (show op) ++ (if i == ip then "  <--- " else "")


separate sep s1 s2 = s1' ++ sep ++ s2'
    where
        s1' = if null s1 then s1 else s1 ++ " "
        s2' = if null s2 then s2 else " " ++ s2

joinWith sep = concat . intersperse sep . map show

(!?) :: [a] -> Int -> Maybe a
xs !? i = if (i >= 0) && (i < length xs) then Just $ xs !! i else Nothing 






iterVM :: VM -> [Either String VM]
iterVM vm = (Right vm) : case step vm of
                            Error e   -> [Left $ "Error: "    ++ e]
                            Stop  r   -> [Left $ "Stopped. "  ++ r]
                            Next  vm' -> iterVM vm'
                            Request f -> [Left $ "Request: " ++ (show f)]


e1 = (eAdd
        (ENum 3)
        (eMul
            (ENum 2)
            (ENum 2)))


-- e2 = (eAdd
--         (ENum 3)
--         (EIfThenElse (eEqual (ENum 1) (ENum 2))
--             (eMul (ENum 2) (ENum 2))
--             (eMul (ENum 3) (ENum 3))))

-- e3 = (eAdd
--         (ENum 1)
--         (ELet "x" (eMul (ENum 2) (ENum 2))
--             (ELet "y" (eMul (ENum 3) (ENum 3))
--                 (eAdd (EVar "x") (EVar "y")) )))


p2 = [

        DDef "add1" ["a"] [
            SReturn (eAdd (EVar "a") (ENum 1))
        ],

        DDef "main" [] [
            SNewVar "x" (ENum 5),
            SNewVar "y" (ENum 10),
            SWhile (eNot (eEqual (EVar "x") (EVar "y"))) [
                SSetVar "x" (EApp "add1" [(EVar "x")])
            ],
            SReturn (EVar "x")
        ]
    
    ]


p3 = [
        {-
        def fib(i) {
            j := 0;
            a := 1; b := 1; c := 0;
            while (not (j == i))) {
                c = a + b;
                a = b;
                b = c;
                j = j + 1;
            }
            return a;
        }
        -}

        -- DDef "fib" ["i"] [
        --     SNewVar "j" (ENum 0),
        --     SNewVar "a" (ENum 1), SNewVar "b" (ENum 1), SNewVar "c" (ENum 0),
        --     SWhile (eNot (eEqual (EVar "j") (EVar "i"))) [
        --         SSetVar "c" (eAdd (EVar "a") (EVar "b")),
        --         SSetVar "a" (EVar "b"),
        --         SSetVar "b" (EVar "c"),
        --         SSetVar "j" (eAdd (EVar "j") (ENum 1))
        --     ],
        --     SReturn (EVar "a")
        -- ],

        {-
        def fib(i) {
            j := 0;
            a := 1; b := 1; c := 0;
            for j from 0 to (i-1) {
                c = a + b;
                a = b;
                b = c;
            }
            return a;
        }
        -}

        DDef "fib" ["i"] [
            SNewVar "j" (ENum 0),
            SNewVar "a" (ENum 1), SNewVar "b" (ENum 1), SNewVar "c" (ENum 0),
            SForFromTo "j" (ENum 0) (eSub (EVar "i") (ENum 1)) [
                SSetVar "c" (eAdd (EVar "a") (EVar "b")),
                SSetVar "a" (EVar "b"),
                SSetVar "b" (EVar "c")
            ],
            SReturn (EVar "a")
        ],

        {-
        def main() {
            return fib(5);
        }
        -}

        DDef "main" [] [
            SReturn (EApp "fib" [ENum 5])
        ]

    ]


p4 = [
        DDef "main" [] [
            SNewVar "i" (ENum 0),
            SForFromTo "i" (ENum 1) (ENum 4) [
                SIfThenElse (eEqual (EVar "i") (ENum 2)) [SContinue] [SPass]
            ],
            SReturn (EVar "i")
        ]

     ]



main = do
    -- let DDef funId args body = defAdd1 in
    --     print $ evalCompile $ compileDef funId args body
    case evalCompile . compileProgram $ p3 of

        Left msg -> do
            print msg

        Right prog -> do
            forM_ (M.toList . allProcs $ prog) $ \(funId, proc) -> do
                print $ funId ++ ":"
                printCode . code $ proc
                blank
            blank
            let vm = execProgram prog
            forM_ (iterVM vm) $ either putStrLn (\x -> putStrLn (prettyShowVM x) >> blank)

    where
        print' x = print x >> blank 
        blank = putStrLn ""
        printCode = mapM putStrLn . map (uncurry showLine) . zip [0..]
        showLine n c = show n ++ "\t" ++ show c

-- main = do
--     let proc = compile e3
--     mapM putStrLn $ map (uncurry showLine) $ zip [0..] $ code proc
--     putStrLn ""
--     mapM print $ unfold1E step (empty {frames = [procFrame proc]})
--     where
--         showLine n c = show n ++ "\t" ++ show c

-- main = mapM print $ unfold1E step (empty {instructions=(code p2), vars=(replicate (nVars p2) 0)})