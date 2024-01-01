using System;
using System.IO;
using System.Diagnostics;
using System.Collections.Generic;
using Microsoft.Z3;
using System.Linq;

namespace State_Estimation
{
    class Estimation
    {
        static TextWriter tw, tw2, tw3;

        Context z3;
        Solver par;

        const String TIME_OUT = "4800000";   // How long we want to search for the model?
        //const String TIME_OUT = "60";   // How long we want to search for the model?
        const int MAX_NUM_SOLUTION = 1;
        int first_time_flag = 1;
        Sort intT, realT, boolT;
        BoolExpr[] CX, SZ, MZ, AZ, CZ, CB;
        IntExpr[] CX2, CZ2, CB2;

        BoolExpr[] ML, RL, FL, SL, EL, IL;
        IntExpr[] EL2, IL2;

        RealExpr[] LP, FDelLP, BDelLP, FDelLPT, BDelLPT, FDelLPM, BDelLPM, DelBP, DelGEN, DelTheta;
        // FDelLPT, BDelLPT for the changes required for topology change (without attack on state estimation)
        // FDelLPM, BDelLPM for attack on state estimation.

        BoolExpr[] BD;  // Knowledge on Line Admittances
        //Term[,] DA, ADA, H, BDA, BADA, BH; 

        #region Input
        //bool[] vBD;
        bool[,] mA, mBA;

        int[,] connected, powerLine, mConnect;
        double[] lineAdmittance, preattackFlow;

        int[] statesToAttack;
        int[,] cnstrOnCXAmt;
        int refBus;
        int nStatesToAttack, nCnstrOnDelTheta, thCZ, thCX, thCB;
        #endregion

        int NBUSES;
        int NLINES;

        int nBuses, nLines, nMeasurements, nDBuses, nGBuses, targetedCase;  // nBuses also represents the number of states.        

        //************************** Added by Shahriar: 08/15/2019 **********************
        /////////// Local variables ////////////////
        int targeted_line;
        int NumAttBus, NumAttLines;
        int[] AttLinesList;
        int[,] AttBusList;

        int[,] BinDB;

        int TotalBinCase;


        const int scalling = 1;
        const double MaxSumOfDeltaLoad = 0.001;

        // const double delta_step_size = 0.001;
        //const double PercentOfDelta = 50;
        //const double stepChangeBPG = 0.001;

        const int THRESHOLD_DIFF = 2;
        double[] demand, maxBPD, minBPD, generation, maxBPG, minBPG, maxPL;
        bool[] mBD, mBG;        // mBG for whether a bus has a generator // mBD for whether a bus has a load  
        double[,] costCoef;
        double ThPGenCost;
        double[,] LODF, SF;
        double minLineOverloadAmount, nPercContgnOverloadLine;
        int numOfLinesOverloaded;
        double PercentOfDelta;
        int TotalBusCombination;


        ///////////// Z3 Variables  //////////////
        RealExpr[] DelBC_REAL, DelBC_ATTACK, DelFPL_REAL, DelFPL_ATTACK;

        RealExpr[] BDem_REAL, BDem_ATTACK, BPow_REAL, BPow_ATTACK, BPGen;
        RealExpr TBPDem_REAL, TDelBP, TDelGEN, PGenCOST;
        RealExpr[] FLP_REAL, BLP_REAL, FLP_ATTACK, BLP_ATTACK;
        RealExpr[] THETA_REAL, THETA_ATTACK;
        RealExpr[,] FLP_CON_REAL, BLP_CON_REAL, FLP_CON_ATTACK, BLP_CON_ATTACK;
        RealExpr[] Lines_Contingency_Flow_Real;
        BoolExpr[] IsOverFlowContgn;
        IntExpr OneSetContgnCount;
        IntExpr[] EachLineContgnCount;

        //********************************   Ends    *****************************************


        // This is only for the simulation
        int nMsrTaken, nMsrSecured;
        const int RATIO = 70;


        // If the verification results SAT output
        bool bSat;

        #region Utility Functions
        // Find whether an item is found in the given domain.
        bool bFind(int[] domain, int item)
        {
            int i;

            for (i = 1; i < domain.Length; i++)
            {
                if (domain[i] == item)
                    return true;
            }

            return false;
        }

        private double LargeNumberDivide(String doubleString)
        {
            /*
            String[] numbers = originalNumber.Split('/');
            if (numbers.Length == 1)
            {
                return Double.Parse(originalNumber);
            }
            else
            {
                return Double.Parse(numbers[0]) / Double.Parse(numbers[1]);
            }
            */
            int numDigists, maxDigits = 16;

            double val = 0.0;
            bool negSign = false;
            String[] parts;

            if (doubleString[0] == '-')
                negSign = true;

            char[] Delims = { '-', '/', ' ' };

            parts = doubleString.Split(Delims, StringSplitOptions.RemoveEmptyEntries);
            if (parts.Length != 2)
            {
                if (parts.Length == 1)
                {
                    if (parts[0].Equals("0"))
                        //Console.WriteLine("Value equal to zero");
                        return 0;
                    else
                    {
                        if (parts[0].Length > maxDigits)
                            parts[0] = parts[0].Remove(parts[0].Length - maxDigits + 1);
                        //Console.WriteLine("Part 0: {0}", parts[0]);
                        double part_0 = Convert.ToDouble(parts[0]);
                        val = part_0;
                        if (negSign)
                            return -val;
                        else
                            return val;
                    }

                }

                Console.WriteLine("ToDouble: Exit due to Wrong Input Format:{0} ", parts.Length);
                Environment.Exit(0);
            }

            if (parts[0].Length > maxDigits || parts[1].Length > maxDigits)
            {
                if (parts[0].Length > parts[1].Length)
                {
                    numDigists = parts[0].Length;
                    parts[1] = parts[1].PadLeft(numDigists, '0');
                }
                else if (parts[0].Length < parts[1].Length)
                {
                    numDigists = parts[1].Length;
                    parts[0] = parts[0].PadLeft(numDigists, '0');
                }
                else
                    numDigists = parts[0].Length;

                parts[0] = parts[0].Remove(maxDigits);
                parts[1] = parts[1].Remove(maxDigits);
            }

            double part0 = Convert.ToDouble(parts[0]);
            double part1 = Convert.ToDouble(parts[1]);

            val = part0 / part1;

            if (negSign)
                return -val;
            else
                return val;
        }


        private long nCr(int n, int r)
        {
            // naive: return Factorial(n) / (Factorial(r) * Factorial(n - r));
            return nPr(n, r) / Factorial(r);
        }

        private long nPr(int n, int r)
        {
            // naive: return Factorial(n) / Factorial(n - r);
            return FactorialDivision(n, n - r);
        }

        private long FactorialDivision(int topFactorial, int divisorFactorial)
        {
            long result = 1;
            for (int i = topFactorial; i > divisorFactorial; i--)
                result *= i;
            return result;
        }

        private long Factorial(int i)
        {
            if (i <= 1)
                return 1;
            return i * Factorial(i - 1);
        }


        #endregion


        // Declaring the basic sorts and terms
        void Declaration()
        {
            int i, j;
            string str;

            intT = z3.MkIntSort();
            realT = z3.MkRealSort();
            boolT = z3.MkBoolSort();

            //**************** Added by Shahriar: 08/15/2019 ****************//

            demand = new double[nBuses + 1];
            maxPL = new double[nLines + 1];

            minBPD = new double[nBuses + 1];
            maxBPD = new double[nBuses + 1];

            generation = new double[nBuses + 1];
            minBPG = new double[nBuses + 1];
            maxBPG = new double[nBuses + 1];

            costCoef = new double[nBuses + 1, 2];
            mBD = new bool[nBuses + 1];
            mBG = new bool[nBuses + 1];

            LODF = new double[nLines, nLines];
            SF = new double[nLines, nBuses - 1];


            //************************  ends  ********************************//

            // Declarations of Expressions
            MZ = new BoolExpr[nMeasurements + 1];
            for (i = 1; i <= nMeasurements; i++)
            {
                MZ[i] = (BoolExpr)z3.MkConst("MZ_" + i, boolT);
            }

            CX = new BoolExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                CX[j] = (BoolExpr)z3.MkConst("CX_" + j, boolT);
            }

            CX2 = new IntExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                CX2[j] = (IntExpr)z3.MkConst("CX2_" + j, intT);
            }

            CZ = new BoolExpr[nMeasurements + 1];
            for (i = 1; i <= nMeasurements; i++)
            {
                CZ[i] = (BoolExpr)z3.MkConst("CZ_" + i, boolT);
            }

            CZ2 = new IntExpr[nMeasurements + 1];
            for (i = 1; i <= nMeasurements; i++)
            {
                CZ2[i] = (IntExpr)z3.MkConst("CZ2_" + i, intT);
            }

            CB = new BoolExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                CB[j] = (BoolExpr)z3.MkConst("CB_" + j, boolT);
            }

            CB2 = new IntExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                CB2[j] = (IntExpr)z3.MkConst("CB2_" + j, intT);
            }

            AZ = new BoolExpr[nMeasurements + 1];
            for (i = 1; i <= nMeasurements; i++)
            {
                AZ[i] = (BoolExpr)z3.MkConst("AZ_" + i, boolT);
            }

            SZ = new BoolExpr[nMeasurements + 1];
            for (i = 1; i <= nMeasurements; i++)
            {
                SZ[i] = (BoolExpr)z3.MkConst("SZ_" + i, boolT);
            }


            // Whenther the admittance of a line is known or not.
            BD = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                BD[i] = (BoolExpr)z3.MkConst("BD_" + i, boolT);
            }


            #region Power Flow and Consumpton Measurements
            FDelLP = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                FDelLP[i] = (RealExpr)z3.MkConst("FDelLinePower_" + i, realT);
            }

            FDelLPT = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                FDelLPT[i] = (RealExpr)z3.MkConst("FDLPowerTopo_" + i, realT);
            }

            FDelLPM = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                FDelLPM[i] = (RealExpr)z3.MkConst("FDLPowerMsr_" + i, realT);
            }

            BDelLP = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                BDelLP[i] = (RealExpr)z3.MkConst("BDelLinePower_" + i, realT);
            }

            BDelLPT = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                BDelLPT[i] = (RealExpr)z3.MkConst("BDLPowerTopo_" + i, realT);
            }

            BDelLPM = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                BDelLPM[i] = (RealExpr)z3.MkConst("BDLPowerMsr_" + i, realT);
            }

            DelBP = new RealExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                DelBP[j] = (RealExpr)z3.MkConst("DelBusPower_" + j, realT);
            }

            DelGEN = new RealExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                DelGEN[j] = (RealExpr)z3.MkConst("DelBusGen_" + j, realT);
            }

            DelTheta = new RealExpr[nBuses + 1];
            for (j = 1; j <= nBuses; j++)
            {
                DelTheta[j] = (RealExpr)z3.MkConst("DelTheta_" + j, realT);
            }

            // Arbitrary line power measurements
            LP = new RealExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                LP[i] = (RealExpr)z3.MkConst("LinePower_" + i, realT);
            }
            #endregion



            //***********  Added by Shahriar: **************//

            TBPDem_REAL = (RealExpr)z3.MkConst("Total_Demand_Real", realT);
            TDelBP = (RealExpr)z3.MkConst("Total_Demand_Attack", realT);
            PGenCOST = (RealExpr)z3.MkConst("Power_Generation_Cost", realT);
            TDelGEN = (RealExpr)z3.MkConst("Total_Power_Generation", realT);


            // Bus Data
            BDem_REAL = new RealExpr[nBuses + 1];
            BDem_ATTACK = new RealExpr[nBuses + 1];
            BPow_REAL = new RealExpr[nBuses + 1];
            BPow_ATTACK = new RealExpr[nBuses + 1];
            BPGen = new RealExpr[nBuses + 1];
            THETA_REAL = new RealExpr[nBuses + 1];
            THETA_ATTACK = new RealExpr[nBuses + 1];

            DelBC_REAL = new RealExpr[nBuses + 1];
            DelBC_ATTACK = new RealExpr[nBuses + 1];

            for (j = 0; j <= nBuses; j++)
            {
                BDem_REAL[j] = (RealExpr)z3.MkConst("Bus_Demand_Real_" + j, realT);
                BDem_ATTACK[j] = (RealExpr)z3.MkConst("Bus_Demand_Attack_" + j, realT);
                BPow_REAL[j] = (RealExpr)z3.MkConst("Bus_Power_Real_" + j, realT);
                BPow_ATTACK[j] = (RealExpr)z3.MkConst("Bus_Power_Attack_" + j, realT);
                BPGen[j] = (RealExpr)z3.MkConst("Bus_Power_Gen_" + j, realT);
                THETA_REAL[j] = (RealExpr)z3.MkConst("THETA_REAL_" + j, realT);
                THETA_ATTACK[j] = (RealExpr)z3.MkConst("THETA_ATTACK_" + j, realT);

                DelBC_REAL[j] = (RealExpr)z3.MkConst("DelBC_REAL" + j, realT);
                DelBC_ATTACK[j] = (RealExpr)z3.MkConst("DelBC_ATTACK" + j, realT);
            }


            FLP_REAL = new RealExpr[nLines + 1];
            BLP_REAL = new RealExpr[nLines + 1];
            FLP_ATTACK = new RealExpr[nLines + 1];
            BLP_ATTACK = new RealExpr[nLines + 1];

            DelFPL_REAL = new RealExpr[nLines + 1];
            DelFPL_ATTACK = new RealExpr[nLines + 1];

            for (i = 0; i <= nLines; i++)
            {
                FLP_REAL[i] = (RealExpr)z3.MkConst("Forward_LinePower_Real_" + i, realT);
                BLP_REAL[i] = (RealExpr)z3.MkConst("Backward_LinePower_Real_" + i, realT);
                FLP_ATTACK[i] = (RealExpr)z3.MkConst("Forward_LinePower_Attack_" + i, realT);
                BLP_ATTACK[i] = (RealExpr)z3.MkConst("Backward_LinePower_Attack_" + i, realT);
                DelFPL_REAL[i] = (RealExpr)z3.MkConst("Delta_Forward_LinePower_Real_" + i, realT);
                DelFPL_ATTACK[i] = (RealExpr)z3.MkConst("Delta_Forward_LinePower_Attack_" + i, realT);
            }

            FLP_CON_REAL = new RealExpr[nLines + 1, nLines + 1];
            BLP_CON_REAL = new RealExpr[nLines + 1, nLines + 1];
            FLP_CON_ATTACK = new RealExpr[nLines + 1, nLines + 1];
            BLP_CON_ATTACK = new RealExpr[nLines + 1, nLines + 1];

            for (i = 0; i <= nLines; i++)
            {
                for (j = 0; j <= nLines; j++)
                {
                    str = string.Format("Forward_Contingencyflow_Real_{0}_{1}", i, j);
                    FLP_CON_REAL[i, j] = (RealExpr)z3.MkConst(str, realT);

                    str = string.Format("Backward_Contingencyflow_Real_{0}_{1}", i, j);
                    BLP_CON_REAL[i, j] = (RealExpr)z3.MkConst(str, realT);

                    str = string.Format("Forward_Contingencyflow_Attack_{0}_{1}", i, j);
                    FLP_CON_ATTACK[i, j] = (RealExpr)z3.MkConst(str, realT);

                    str = string.Format("Backward_Contingencyflow_Attack_{0}_{1}", i, j);
                    BLP_CON_ATTACK[i, j] = (RealExpr)z3.MkConst(str, realT);
                }

            }


            Lines_Contingency_Flow_Real = new RealExpr[nLines + 1];
            for (i = 0; i <= nLines; i++)
            {
                Lines_Contingency_Flow_Real[i] = (RealExpr)z3.MkConst("Lines_Contingency_Flow_Real_" + i, realT);
            }

            OneSetContgnCount = (IntExpr)z3.MkConst("OneSetContgnCount", intT);

            IsOverFlowContgn = new BoolExpr[nLines + 1];
            EachLineContgnCount = new IntExpr[nLines + 1];

            for (i = 0; i <= nLines; i++)
            {
                IsOverFlowContgn[i] = (BoolExpr)z3.MkConst("Is_OverFlow_Contingency_" + i, boolT);
                EachLineContgnCount[i] = (IntExpr)z3.MkConst("EachLineContingency_" + i, intT);
            }

            //**************************************   Ends  *********************************************//

            #region Modeling Topology Attack (based on Lines)
            // Whether a line is considered in the topology
            ML = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                ML[i] = (BoolExpr)z3.MkConst("ML_" + i, boolT);
            }

            // Whenther a line really does exist.
            RL = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                RL[i] = (BoolExpr)z3.MkConst("RL_" + i, boolT);
            }

            // Whether an existing line is excluded from the topology by injecting false data
            EL = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                EL[i] = (BoolExpr)z3.MkConst("EL_" + i, boolT);
            }

            EL2 = new IntExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                EL2[i] = (IntExpr)z3.MkConst("EL2_" + i, intT);
            }

            // Whether a non-existing line is included in the topology by injecting false data
            IL = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                IL[i] = (BoolExpr)z3.MkConst("IL_" + i, boolT);
            }

            IL2 = new IntExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                IL2[i] = (IntExpr)z3.MkConst("IL2_" + i, intT);
            }

            // Whether a line is secured from injecting false data
            SL = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                SL[i] = (BoolExpr)z3.MkConst("SL_" + i, boolT);
            }

            // Whether a line is fixed (core), i.e., the line is always open.
            FL = new BoolExpr[nLines + 1];
            for (i = 1; i <= nLines; i++)
            {
                FL[i] = (BoolExpr)z3.MkConst("FL_" + i, boolT);
            }


            #endregion

        }


        // Read input from the file

        void ReadInput()
        {
            String line;
            String[] lineElement;

            int i, j;
            Random rand = new Random();

            try
            {


                System.IO.StreamReader file_target = new System.IO.StreamReader(String.Format("Input_Target.txt"));
                char[] delims = { ' ', ',', '\t' };

                #region Number of Buses, Lines, and the Reference Bus
                while (true)
                {
                    if ((line = file_target.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 2)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input~{0}", lineElement);
                        Environment.Exit(0);
                    }

                    NBUSES = Convert.ToInt32(lineElement[0]);
                    NLINES = Convert.ToInt32(lineElement[1]);
                    if (first_time_flag == 1)
                    {
                        Console.WriteLine("Number of Buses: {0}, Lines: {1}", NBUSES, NLINES);
                        first_time_flag = 0;
                    }
                    break;
                }
                #endregion



                System.IO.StreamReader file = new System.IO.StreamReader(String.Format("Input_Topo_{0}_{1}.txt", NBUSES, NLINES));
                System.IO.StreamReader lodf_file = new System.IO.StreamReader(String.Format("input_LODF_{0}_{1}.txt", NBUSES, NLINES));
                System.IO.StreamReader sf_file = new System.IO.StreamReader(String.Format("input_SF_{0}_{1}.txt", NBUSES, NLINES));



                #region Number of Buses, Lines, and the Reference Bus, targetedCase
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 5)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input~~~~{0}", lineElement);
                        Environment.Exit(0);
                    }

                    nBuses = Convert.ToInt32(lineElement[0]);
                    nLines = Convert.ToInt32(lineElement[1]);
                    nMeasurements = 2 * nLines + nBuses;

                    refBus = Convert.ToInt32(lineElement[2]);
                    NumAttBus = Convert.ToInt32(lineElement[3]);
                    targetedCase = Convert.ToInt32(lineElement[4]);

                    break;
                }
                #endregion

                #region Initializations
                {
                    Declaration();

                    //vBD = new bool[nLines + 1];
                    mA = new bool[nLines + 1, nBuses + 1];
                    mBA = new bool[nLines + 1, nBuses + 1];


                    powerLine = new int[nLines + 1, 2];  // The first two entries are for the end buses.
                    lineAdmittance = new double[nLines + 1];
                    preattackFlow = new double[nLines + 1];
                    connected = new int[nLines + 1, nLines + 1];
                    // A bus is connected with which bus. First element is the number of connected buses.
                    mConnect = new int[nBuses + 1, nBuses + 1];
                    for (i = 1; i <= nBuses; i++)
                        for (j = 1; j <= nBuses; j++)
                            mConnect[i, j] = 0;
                }
                #endregion

                #region Line Properties
                int from, to;
                double admt, lineCap, linflow;
                bool admtK, rL, fL, sL;
                //Console.WriteLine("Number of line:");

                i = 1;  // Number of line
                while (i <= nLines)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 10)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input~{0}", line);
                        Environment.Exit(0);
                    }

                    //k = Convert.ToInt32(lineElement[0]);  // Line No, what we assume equal to i
                    from = Convert.ToInt32(lineElement[1]);
                    to = Convert.ToInt32(lineElement[2]);
                    admt = Convert.ToDouble(lineElement[3]);
                    lineCap = Convert.ToDouble(lineElement[4]);
                    linflow = Convert.ToDouble(lineElement[5]);
                    admtK = Convert.ToBoolean(Convert.ToInt32(lineElement[6]));
                    rL = Convert.ToBoolean(Convert.ToInt32(lineElement[7]));
                    fL = Convert.ToBoolean(Convert.ToInt32(lineElement[8]));
                    sL = Convert.ToBoolean(Convert.ToInt32(lineElement[9]));

                    powerLine[i, 0] = from;
                    powerLine[i, 1] = to;
                    lineAdmittance[i] = admt;
                    maxPL[i] = lineCap * scalling;
                    preattackFlow[i] = linflow * scalling;
                    mConnect[from, to] = mConnect[to, from] = i;

                    if ((from != 0) && (to != 0))
                    {
                        connected[from, 0]++;
                        connected[from, connected[from, 0]] = to;

                        connected[to, 0]++;
                        connected[to, connected[to, 0]] = from;
                    }

                    if (admtK)
                        par.Assert(BD[i]);
                    else
                        par.Assert(z3.MkNot(BD[i]));

                    if (rL)
                        par.Assert(RL[i]);
                    else
                        par.Assert(z3.MkNot(RL[i]));

                    if (fL)
                        par.Assert(FL[i]);
                    else
                        par.Assert(z3.MkNot(FL[i]));

                    //z3.AssertCnstr(ML[i]);

                    if (sL)
                        par.Assert(SL[i]);
                    else
                        par.Assert(z3.MkNot(SL[i]));

                    i++;
                }

                // Knowledge Calaculation on Connectivity 
                for (i = 1; i <= nLines; i++)
                {
                    from = powerLine[i, 0];
                    to = powerLine[i, 1];
                    admt = lineAdmittance[i];

                    if ((from != 0) && (to != 0))
                    {
                        for (j = 1; j <= nBuses; j++)
                        {
                            //z3.AssertCnstr(BA[i, j]);
                            mBA[i, j] = true;
                            if ((j == from) || (j == to))
                            {
                                //z3.AssertCnstr(A[i, j]);
                                mA[i, j] = true;
                            }
                            else
                            {
                                //z3.AssertCnstr(z3.MkNot(A[i, j]));
                                mA[i, j] = false;
                            }
                        }
                    }
                    else if ((from != 0) || (to != 0))
                    {
                        int[] connectedBuses = new int[nBuses + 1];
                        for (j = 1; j <= nBuses; j++)
                            connectedBuses[j] = -1;

                        int known;
                        if (from != 0)
                            known = from;
                        else
                            known = to;

                        connectedBuses[known] = 1;

                        for (j = 1; j <= connected[known, 0]; j++)
                        {
                            connectedBuses[connected[known, j]] = 0;
                        }

                        for (j = 1; j <= nBuses; j++)
                        {
                            if (connectedBuses[j] == 1)
                            {
                                //z3.AssertCnstr(A[i, j]);
                                //z3.AssertCnstr(BA[i, j]);
                                mA[i, j] = true;
                                mBA[i, j] = true;
                            }
                            else if (connectedBuses[j] == 0)
                            {
                                //z3.AssertCnstr(z3.MkNot(A[i, j]));
                                //z3.AssertCnstr(BA[i, j]);
                                mA[i, j] = false;
                                mBA[i, j] = true;
                            }
                            else
                            {
                                //z3.AssertCnstr(A[i, j]);
                                //z3.AssertCnstr(z3.MkNot(BA[i, j]));
                                mA[i, j] = true;
                                mBA[i, j] = false;
                            }
                        }
                    }
                    else
                    {
                        for (j = 1; j <= nBuses; j++)
                        {
                            //z3.AssertCnstr(z3.MkNot(BA[i, j]));
                            //z3.AssertCnstr(A[i, j]);
                            mA[i, j] = true;
                            mBA[i, j] = false;
                        }
                    }
                }
                #endregion

                #region Generation and load bus
                {
                    nGBuses = 0;
                    nDBuses = 0;

                    i = 1;  // Bus No        
                    bool bBLoad, bBGen;
                    while (i <= nBuses)
                    {
                        if ((line = file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        //Console.Write(lineElement.Length + " ");
                        if (lineElement.Length != 3)
                        {
                            Console.WriteLine("Exit due to Wrong Number of Input (BUS/LOAD)");
                            Environment.Exit(0);
                        }

                        //k = Convert.ToInt32(lineElement[0]);  // Measurement No, what we assume equal to i
                        bBGen = Convert.ToBoolean(Convert.ToInt32(lineElement[1]));
                        bBLoad = Convert.ToBoolean(Convert.ToInt32(lineElement[2]));

                        if (bBGen)
                        {
                            //s.Assert(BG[i]);
                            mBG[i] = true;
                            nGBuses++;
                        }
                        else
                            mBG[i] = false;
                        //s.Assert(z3.MkNot(BG[i]));


                        if (bBLoad)
                        {
                            //s.Assert(BD[i]);
                            mBD[i] = true;
                            nDBuses++;
                        }
                        else
                            mBD[i] = false;
                        //s.Assert(z3.MkNot(BD[i]));

                        i++;

                    }

                    int k;  // Bus No

                    // Generation buses                                        
                    if (nGBuses > 0)
                    {
                        for (i = 1; i <= nGBuses; i++)
                        {
                            while (true)
                            {
                                if ((line = file.ReadLine()) == null)
                                {
                                    Console.WriteLine("Exit due to Insufficient Input");
                                    Environment.Exit(0);
                                }

                                line = line.Trim();
                                if ((line.Length == 0) || line.StartsWith("#"))
                                    continue;

                                lineElement = line.Split(delims);
                                if (lineElement.Length != 6)
                                {
                                    Console.WriteLine("Exit due to Wrong Number of Input: generation: {0}", nGBuses);
                                    Environment.Exit(0);
                                }

                                k = Convert.ToInt32(lineElement[0]);

                                


                                //Console.WriteLine("Orginial at Bus {0} is {1} with {2}", k, Convert.ToDouble(lineElement[1]), scalling);
                                //Console.WriteLine("Generation at Bus {0} is {1}", k, generation[k]);

                                maxBPG[k] = Convert.ToDouble(lineElement[1]) * scalling;
                                minBPG[k] = Convert.ToDouble(lineElement[2]) * scalling;
                                costCoef[k, 0] = Convert.ToDouble(lineElement[3]);
                                costCoef[k, 1] = Convert.ToDouble(lineElement[4]);
                                generation[k] = Convert.ToDouble(lineElement[5]) * scalling;
                                //STEPS[k] = Convert.ToInt32((maxBPG[k] - minBPG[k]) / stepChangeBPG);
                                //stepChangeBPG[k] = (maxBPG[k] - minBPG[k]) / STEPS;
                                break;
                            }
                        }
                    }

                    // Load buses
                    if (nDBuses > 0)
                    {
                        for (i = 1; i <= nDBuses; i++)
                        {
                            if ((line = file.ReadLine()) == null)
                            {
                                Console.WriteLine("Exit due to Insufficient Input");
                                Environment.Exit(0);
                            }

                            line = line.Trim();
                            if ((line.Length == 0) || line.StartsWith("#"))
                            {
                                i--;
                                continue;
                            }


                            lineElement = line.Split(delims);

                            if (lineElement.Length != 4)
                            {
                                Console.WriteLine("Exit due to Wrong Number of Input at bus");
                                Environment.Exit(0);
                            }

                            k = Convert.ToInt32(lineElement[0]);
                            demand[k] = Convert.ToDouble(lineElement[1]) * scalling;
                            maxBPD[k] = Convert.ToDouble(lineElement[2]) * scalling;
                            minBPD[k] = Convert.ToDouble(lineElement[3]) * scalling;

                        }



                    }
                }
                #endregion

                #region Measurement Poperties
                i = 1;  // Measurement No
                int msrTaken, secured, attackerCan;
                nMsrTaken = 0;
                nMsrSecured = 0;
                while (i <= nMeasurements)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 4)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input: msr: {0}", nMeasurements);
                        Environment.Exit(0);
                    }

                    //k = Convert.ToInt32(lineElement[0]);  // Measurement No, what we assume equal to i
                    msrTaken = Convert.ToInt32(lineElement[1]);

                    // This is only for the simulation //
                    //int r = rand.Next(100);
                    //if (r < RATIO)
                    //    msrTaken = 1;
                    //else
                    //    msrTaken = 0;
                    /////////////////////////////////////

                    if (msrTaken != 0) // Measurement is taken
                    {
                        nMsrTaken++;

                        par.Assert(MZ[i]);

                        secured = Convert.ToInt32(lineElement[2]);
                        // This is only for the simulation //
                        //int r = rand.Next(100);
                        //if (r < RATIO)
                        //    secured = 1;
                        //else
                        //    secured = 0;
                        /////////////////////////////////////

                        if (secured != 0) // Secured
                        {
                            nMsrSecured++;
                            par.Assert(SZ[i]);
                        }
                        else // Not secured
                            par.Assert(z3.MkNot(SZ[i]));

                        attackerCan = Convert.ToInt32(lineElement[3]);
                        if (attackerCan != 0) // Attacker has the ability to attack
                            par.Assert(AZ[i]);
                        else // Attacker has no ability to attack
                            par.Assert(z3.MkNot(AZ[i]));
                    }
                    else // Measurement is not taken
                    {
                        par.Assert(z3.MkNot(MZ[i]));
                        par.Assert(z3.MkNot(SZ[i]));
                        par.Assert(z3.MkNot(AZ[i]));
                    }

                    i++;
                }
                #endregion

                #region Cost Contraint
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    ThPGenCost = Convert.ToDouble(lineElement[0]);

                    break;
                }
                #endregion

                #region Percent of Delta Load
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    PercentOfDelta = Convert.ToDouble(lineElement[0]);

                    break;
                }
                #endregion

                #region Attacker's Goal
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 2)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input Line Overload");
                        Environment.Exit(0);
                    }

                    minLineOverloadAmount = Convert.ToDouble(lineElement[0]);

                    numOfLinesOverloaded = Convert.ToInt32(lineElement[1]);
                    nPercContgnOverloadLine = numOfLinesOverloaded;
                    //Console.WriteLine("numOfLinesOverloaded: {0}", numOfLinesOverloaded);
                    //****************** edited **************
                    //nPercContgnOverloadLine = Convert.ToDouble(lineElement[1]);
                    //numOfLinesOverloaded = (int)Math.Ceiling(nPercContgnOverloadLine * nLines / 100.0);
                    //****************************************

                    //Console.WriteLine("numOfLinesOverloaded: {0}", numOfLinesOverloaded);

                    //Console.WriteLine("Number of Lines to be overloaded: {0}", numOfLinesOverloaded);

                    break;
                }
                #endregion


                #region Chosen States for Attack
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    nStatesToAttack = Convert.ToInt32(lineElement[0]);

                    break;
                }

                if (nStatesToAttack > 0)
                {
                    while (true)
                    {
                        if ((line = file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        if (lineElement.Length != nStatesToAttack)
                        {
                            Console.WriteLine("Exit due to Wrong Number of Input");
                            Environment.Exit(0);
                        }

                        int[] selected4UFDI = new int[nBuses + 1];
                        for (i = 1; i <= nBuses; i++)
                            selected4UFDI[i] = 0;

                        statesToAttack = new int[nStatesToAttack + 1];
                        for (i = 1; i <= nStatesToAttack; i++)
                        {
                            statesToAttack[i] = Convert.ToInt32(lineElement[i - 1]);
                            selected4UFDI[statesToAttack[i]] = 1;
                            //par.Assert(CX[statesToAttack[i]]);
                        }


                        break;
                    }
                }
                #endregion

                #region Maximum number of states for attack
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    thCX = Convert.ToInt32(lineElement[0]);
                    //thCX = NumAttBus;
                    break;
                }
                #endregion

                #region Constraints on seletected states
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 1)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    nCnstrOnDelTheta = Convert.ToInt32(lineElement[0]);

                    break;
                }

                if (nCnstrOnDelTheta > 0)
                {
                    cnstrOnCXAmt = new int[nCnstrOnDelTheta + 1, 3];
                    for (i = 1; i <= nCnstrOnDelTheta; i++)
                    {
                        while (true)
                        {
                            if ((line = file.ReadLine()) == null)
                            {
                                Console.WriteLine("Exit due to Insufficient Input");
                                Environment.Exit(0);
                            }

                            line = line.Trim();
                            if ((line.Length == 0) || line.StartsWith("#"))
                                continue;

                            lineElement = line.Split(delims);
                            if (lineElement.Length != 3)
                            {
                                Console.WriteLine("Exit due to Wrong Number of Input");
                                Environment.Exit(0);
                            }

                            cnstrOnCXAmt[i, 0] = Convert.ToInt32(lineElement[0]);
                            cnstrOnCXAmt[i, 1] = Convert.ToInt32(lineElement[1]);
                            cnstrOnCXAmt[i, 2] = Convert.ToInt32(lineElement[2]);

                            break;
                        }
                    }
                }
                #endregion


                #region Attacker's Resource Limitation
                while (true)
                {
                    if ((line = file.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);
                    if (lineElement.Length != 2)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input");
                        Environment.Exit(0);
                    }

                    thCZ = Convert.ToInt32(lineElement[0]);
                    thCB = Convert.ToInt32(lineElement[1]);
                    //thCB = NumAttBus;
                    //z3.AssertCnstr(z3.MkEq(TH, z3.MkNumeral(th, intT));

                    break;
                }
                #endregion


                file.Close();

                #region Input LODF Matrix

                for (int l = 0; l < nLines; l++)
                {
                    while (true)
                    {
                        if ((line = lodf_file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        if (lineElement.Length != nLines)
                        {
                            Console.WriteLine("Exit due to Wrong Number of Input: LODF: {0}", lineElement.Length);
                            Environment.Exit(0);
                        }

                        for (int k = 0; k < lineElement.Length; k++)
                        {
                            LODF[l, k] = Convert.ToDouble(lineElement[k]);
                        }

                        break;
                    }
                }

                lodf_file.Close();

                #endregion

                #region Input SF Matrix

                for (int l = 0; l < nLines; l++)
                {
                    while (true)
                    {
                        if ((line = sf_file.ReadLine()) == null)
                        {
                            Console.WriteLine("Exit due to Insufficient Input");
                            Environment.Exit(0);
                        }

                        line = line.Trim();
                        if ((line.Length == 0) || line.StartsWith("#"))
                            continue;

                        lineElement = line.Split(delims);
                        if (lineElement.Length != nBuses - 1)
                        {
                            Console.WriteLine("Exit due to Wrong Number of Input: SF: {0}", lineElement.Length);
                            Environment.Exit(0);
                        }

                        for (int k = 0; k < lineElement.Length; k++)
                        {
                            SF[l, k] = Convert.ToDouble(lineElement[k]);
                        }

                        break;
                    }
                }

                sf_file.Close();

                #endregion

            }
            catch (Exception e)
            {
                throw e;
                //Console.WriteLine(e.Message);
                //Environment.Exit(0);
            }

            System.IO.StreamReader line_bus_list = new System.IO.StreamReader(String.Format("input_Lines_Buses_{0}_{1}_{2}.txt", NBUSES, NLINES, NumAttBus));
            try
            {
                //TotalBusCombination = (int)(nCr(nBuses, NumAttBus));
                TotalBusCombination = 100;
            }
            catch (Exception e)
            {
                TotalBusCombination = 100;
            }
            //Console.WriteLine("TotalBusCombination= {0}", TotalBusCombination);
            //TotalBusCombination = 1;
            //Console.WriteLine("TotalBusCombination= {0}", TotalBusCombination);

            AttBusList = new int[TotalBusCombination, NumAttBus];
            char[] delimss = { ' ', ',', '\t' };


            try
            {
                #region List of Lines to be considered
                while (true)
                {
                    if ((line = line_bus_list.ReadLine()) == null)
                    {
                        Console.WriteLine("Exit due to Insufficient Input");
                        Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delimss);
                    NumAttLines = lineElement.Length;
                    AttLinesList = new int[NumAttLines];
                    AttLinesList = Array.ConvertAll(lineElement, int.Parse);
                    break;
                }
                #endregion

                #region  List of sets of Attacked buses
                int k = 0;
                while (true)
                {
                    if ((line = line_bus_list.ReadLine()) == null)
                    {
                        TotalBusCombination = k;
                        //Console.WriteLine("TotalBusCombination: {0}", TotalBusCombination);

                        break;
                        //Environment.Exit(0);
                    }

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delimss);
                    //Console.WriteLine("{0}", NumAttBus);
                    if (lineElement.Length != NumAttBus)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input: NumAttBus {0}-lineElement.Length {1}", NumAttBus, lineElement.Length);
                        Environment.Exit(0);
                    }
                    for (int l = 0; l < lineElement.Length; l++)
                    {
                        AttBusList[k, l] = Convert.ToInt32(lineElement[l]);
                    }
                    k++;

                }
                #endregion

            }
            catch (Exception e)
            {
                Console.WriteLine(e.Message);
                Environment.Exit(0);
                throw e;


            }
        }

        void ReadBinDB()
        {
            String line;
            String[] lineElement;
            var listofcases = new List<string>();

            try
            {
                System.IO.StreamReader file_targetbn = new System.IO.StreamReader(String.Format("Binary_DataBase.txt"));

                char[] delims = { ' ', ',', '\t' };

                #region  List of Attacked Bus Data Base
                int k = 0;
                while (true)
                {

                    if ((line = file_targetbn.ReadLine()) == null)
                    {
                        //Console.WriteLine("Reading bin data set: Null");
                        TotalBinCase = k;
                        break;
                    }

                    //Console.WriteLine("{0}", line);

                    line = line.Trim();
                    if ((line.Length == 0) || line.StartsWith("#"))
                        continue;

                    lineElement = line.Split(delims);

                    if (lineElement.Length != NBUSES + 2)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input: BN");
                        Environment.Exit(0);
                    }
                    listofcases.Add(line);


                    k++;

                }


                string[] arrayOfStrings = listofcases.ToArray();
                k = 0;
                BinDB = new int[TotalBinCase, NBUSES + 2];

                while (k < TotalBinCase)
                {

                    lineElement = arrayOfStrings[k].Split(delims);
                    if (lineElement.Length != NBUSES + 2)
                    {
                        Console.WriteLine("Exit due to Wrong Number of Input: BN");
                        Environment.Exit(0);
                    }

                    for (int l = 0; l < lineElement.Length; l++)
                    {
                        //Console.WriteLine("Reading bin data set: Ekhanei somossa");
                        //Console.WriteLine("{0}", lineElement[l]);
                        //listofcases.Add(line);
                        BinDB[k, l] = Convert.ToInt32(lineElement[l]);
                        //Console.WriteLine("Reading bin data set: Holo na");

                    }
                    k++;

                }
                Console.WriteLine("Database Load done !");

            }
            #endregion


            catch (Exception e)
            {
                Console.WriteLine("Reading bin data set: Exception");
                Console.WriteLine(e.Message);
                Environment.Exit(0);
                throw e;

            }
        }

        void Formalize(int Line_count, int Bus_count)
        {
            int i, j, k, l;

            RealExpr RZero = z3.MkReal(0);
            IntExpr IZero = z3.MkInt(0);

            targeted_line = AttLinesList[Line_count];
            //Console.Write("Target Line: {0}\n", targeted_line);
            // Console.WriteLine("\n\nTargeted Line: {0}\n\n", targeted_line);

            #region Total Change in Power Flow Measurements Depends on Topology Change and Attack.
            {
                BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                for (i = 1; i <= nLines; i++)
                {
                    Exprs[2 * i - 2] = z3.MkEq(FDelLP[i], z3.MkAdd(FDelLPT[i], FDelLPM[i]));
                    Exprs[2 * i - 1] = z3.MkEq(BDelLP[i], z3.MkAdd(BDelLPT[i], BDelLPM[i]));
                }

                BoolExpr Expr = z3.MkAnd(Exprs);
                par.Assert(Expr);
                //tw.WriteLine("(assert {0})", Expr.ToString());
            }
            #endregion

            #region [commented] Ultimate Topology after Line Exclusion or Inclusion Attack
            /*
            {
                // When an exclusion attack is possible
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(EL[i], z3.MkAnd(new BoolExpr[] { RL[i], z3.MkNot(FL[i]), z3.MkNot(SL[i]) }));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                // When an inclusion attack is possible
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(IL[i], z3.MkAnd(z3.MkNot(RL[i]), z3.MkNot(SL[i])));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                   //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                // When a line is considered in the state estimation
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(z3.MkOr(z3.MkAnd(RL[i], z3.MkNot(EL[i])),
                            z3.MkAnd(z3.MkNot(RL[i]), IL[i])), ML[i]);
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                //////////////////////// Ashiq on 11/15/2015 [Start] ///////////////////////
                // When a line is not considered in the state estimation
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(ML[i], z3.MkOr(z3.MkAnd(RL[i], z3.MkNot(EL[i])),
                            z3.MkAnd(z3.MkNot(RL[i]), IL[i])));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                   // par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                //////////////////////// Ashiq on 11/15/2015 [End] ////////////////////////
            }
            #endregion

            #region Topology Attack has impacts on False Data Injection
            {
                // Expected Changes on Power Flow Measurements
                // When there is no Topology Change
                {
                    BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[2 * i - 2] = z3.MkImplies(z3.MkNot(z3.MkOr(EL[i], IL[i])), z3.MkEq(FDelLPT[i], RZero));
                        Exprs[2 * i - 1] = z3.MkImplies(z3.MkNot(z3.MkOr(EL[i], IL[i])), z3.MkEq(BDelLPT[i], RZero));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                // When there is a Topology Change
                {
                    // When there is a Line Exclusion 
                    {
                        BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                        for (i = 1; i <= nLines; i++)
                        {
                            double lp = lineAdmittance[i] * (thetas[powerLine[i, 0]] - thetas[powerLine[i, 1]]);
                            Exprs[2 * i - 2] = z3.MkImplies(EL[i], z3.MkEq(FDelLPT[i], z3.MkNumeral(Convert.ToString(-lp), realT)));
                            Exprs[2 * i - 1] = z3.MkImplies(EL[i], z3.MkEq(BDelLPT[i], z3.MkNumeral(Convert.ToString(lp), realT)));
                        }

                        BoolExpr Expr = z3.MkAnd(Exprs);
                        //par.Assert(Expr);
                        //tw.WriteLine("(assert {0})", Expr.ToString());
                    }

                    // When there is a Line Inclusion
                    {
                        BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                        for (i = 1; i <= nLines; i++)
                        {
                            double lp = lineAdmittance[i] * (thetas[powerLine[i, 0]] - thetas[powerLine[i, 1]]);
                            Exprs[2 * i - 2] = z3.MkImplies(IL[i], z3.MkEq(FDelLPT[i], z3.MkNumeral(Convert.ToString(lp), realT)));
                            Exprs[2 * i - 1] = z3.MkImplies(IL[i], z3.MkEq(BDelLPT[i], z3.MkNumeral(Convert.ToString(-lp), realT)));
                        }

                        BoolExpr Expr = z3.MkAnd(Exprs);
                        //par.Assert(Expr);
                        //tw.WriteLine("(assert {0})", Expr.ToString());
                    }
                }

                // When a Line is not Considered
                {
                    BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[2 * i - 2] = z3.MkImplies(z3.MkNot(ML[i]), z3.MkEq(FDelLPM[i], RZero));
                        Exprs[2 * i - 1] = z3.MkImplies(z3.MkNot(ML[i]), z3.MkEq(BDelLPM[i], RZero));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
            }
            */
            #endregion

            #region False Data Injection Attack on Measurements
            {
                #region The change of a line power measurement depends on the phasor changes.
                
                {
                    BoolExpr[] Exprs = new BoolExpr[2 * nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        /*
                        Exprs[2 * i - 2] = z3.MkEq(FDelLPM[i],
                            z3.MkMul(z3.MkSub(DelTheta[powerLine[i, 0]], DelTheta[powerLine[i, 1]]),
                                z3.MkReal(Convert.ToString(lineAdmittance[i]))));

                        Exprs[2 * i - 1] = z3.MkEq(BDelLPM[i],
                            z3.MkMul(z3.MkSub(DelTheta[powerLine[i, 1]], DelTheta[powerLine[i, 0]]),
                                z3.MkReal(Convert.ToString(lineAdmittance[i]))));
                        */
                        Exprs[2 * i - 2] = z3.MkEq(FDelLPM[i], DelFPL_ATTACK[i]);

                        Exprs[2 * i - 1] = z3.MkEq(BDelLPM[i], z3.MkSub(RZero, DelFPL_ATTACK[i])); 
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                
                #endregion

                #region The change of a bus consumption measurement depends on the changes of the connected lines.
                
                {
                    for (j = 1; j <= nBuses; j++)
                    {
                        ArithExpr[] Exprs = new ArithExpr[connected[j, 0]];
                        for (i = 1; i <= connected[j, 0]; i++)
                        {
                            k = mConnect[j, connected[j, i]];
                            if (j == powerLine[k, 0])
                                Exprs[i - 1] = FDelLPM[k];
                            else
                                Exprs[i - 1] = BDelLPM[k];
                        }

                        BoolExpr Expr = z3.MkEq(DelBC_ATTACK[j], z3.MkAdd(Exprs));
                        par.Assert(Expr);
                        //tw.WriteLine("(assert {0})", Expr.ToString());
                    }
                }
                
                #endregion

                //********************* Added By Shahriar  ************************//

                // REAL AND ATTACK LOAD DATA
                #region [commented ]Bus Real Demand
                /*
                 {
                    // Individul bus demand
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        if (mBD[j])
                            Exprs[j - 1] = z3.MkEq(BDem_REAL[j], z3.MkReal(Convert.ToString(demand[j])));
                        else
                            Exprs[j - 1] = z3.MkEq(BDem_REAL[j], RZero);
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }

                {   // Total bus demand
                    RealExpr[] Exprs = new RealExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = BDem_REAL[j];
                    }

                    BoolExpr Expr = z3.MkEq(TBPDem_REAL, z3.MkAdd(Exprs));
                    par.Assert(Expr);
                }
                */
                #endregion

                // Delta_Steps_Count should be within the limit of forward and backward steps ( shahriar )
                #region [commented] Delta in Steps 
                /*
                {
                    for (int j = 1; j <= nBuses; j++)
                    {

                        par.Assert(z3.MkImplies(VULNERABLE_BUSES[j], z3.MkAnd(z3.MkLe(Delta_Steps_Count[j], z3.MkInt(Convert.ToString(forward_steps[j]))), z3.MkGe(Delta_Steps_Count[j], z3.MkInt(Convert.ToString(backward_steps[j]))))));
                        par.Assert(z3.MkImplies(z3.MkNot(VULNERABLE_BUSES[j]), z3.MkEq(Delta_Steps_Count[j], z3.MkInt(Convert.ToString(Zero)))));

                    }
                }

                // Delta Load = Delta_step*MIN_DELTA ( shahriar )
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (int j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = z3.MkEq(Delta_Load[j], z3.MkMul(Delta_Steps_Count[j], z3.MkReal(Convert.ToString(MIN_DELTA))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                */
                #endregion

                #region Sum of delta load (DelBP) should be almost zero(threshold)
                {
                    RealExpr[] Exprs = new RealExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = DelBP[j];
                    }
                    BoolExpr Expr = z3.MkAnd(z3.MkGe(z3.MkAdd(Exprs), z3.MkReal(Convert.ToString(-MaxSumOfDeltaLoad))),
                    z3.MkLe(z3.MkAdd(Exprs), z3.MkReal(Convert.ToString(MaxSumOfDeltaLoad))));
                    par.Assert(Expr);
                }
                #endregion

                #region Delta Load (DelBP) should be within a percent of origianl load
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        double minDeltaLimit = 0.005;
                        double maxDelta = demand[j] * PercentOfDelta / 100;
                        double minDelta = -demand[j] * PercentOfDelta / 100;

                        if (demand[j] < 0)
                        {
                            minDeltaLimit = -minDeltaLimit;
                            maxDelta = -maxDelta;
                            minDelta = -minDelta;
                            //Console.WriteLine("{0}, {1}, {2}", maxDelta, minDelta, minDeltaLimit);
                        }
                        


                        //Console.WriteLine("{0} and {1}", maxDelta, minDelta);
                        //Exprs[j - 1] = z3.MkLe(DelBP[j], z3.MkMul(BDem_REAL[j], z3.MkReal(Convert.ToString(PercentOfDelta / 100))));
                        Exprs[j - 1] = z3.MkOr(
                            z3.MkAnd(z3.MkLe(DelBP[j], z3.MkReal(Convert.ToString(maxDelta))), z3.MkGe(DelBP[j], z3.MkReal(Convert.ToString(minDeltaLimit)))),
                            z3.MkAnd(z3.MkLe(DelBP[j], z3.MkReal(Convert.ToString(-minDeltaLimit))), z3.MkGe(DelBP[j], z3.MkReal(Convert.ToString(minDelta)))),
                            z3.MkEq(DelBP[j], z3.MkReal(Convert.ToString(0))));
                            

                        //Exprs[j - 1] = z3.MkAnd(z3.MkLe(DelBP[j], z3.MkReal(Convert.ToString(maxDelta))), z3.MkGe(DelBP[j], z3.MkReal(Convert.ToString(minDelta))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion

                #region Attacked Demand, BDem_ATTACK = BDem_REAL + DelBP

                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        //Exprs[j - 1] = z3.MkEq(BDem_ATTACK[j], z3.MkAdd(BDem_REAL[j], DelBP[j]));
                        Exprs[j - 1] = z3.MkEq(BDem_ATTACK[j], z3.MkAdd(z3.MkReal(Convert.ToString(demand[j])), DelBP[j]));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion

                #region Max/Min Limit of Attacked_Demand
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = z3.MkAnd(z3.MkGe(BDem_ATTACK[j], z3.MkReal(Convert.ToString(minBPD[j]))),
                            z3.MkLe(BDem_ATTACK[j], z3.MkReal(Convert.ToString(maxBPD[j]))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion

                #region Total Delta AttackDemand, TDelBP=  SUM OF Delta DelBP
                {
                    RealExpr[] Exprs = new RealExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = DelBP[j];
                    }
                    BoolExpr Expr = z3.MkEq(TDelBP, z3.MkAdd(Exprs));
                    par.Assert(Expr);
                }

                #endregion

                // GENERATION DATA

                #region BUS GENERATION- Max and Min Limit of Generation  [need some attention later: steps??]
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        if (mBG[j])
                            Exprs[j - 1] =
                                z3.MkOr(
                                    z3.MkAnd(
                                        z3.MkGe(BPGen[j], z3.MkReal(Convert.ToString(minBPG[j]))),
                                        z3.MkLe(BPGen[j], z3.MkReal(Convert.ToString(maxBPG[j])))),
                                  z3.MkEq(BPGen[j], RZero));
                        else
                            Exprs[j - 1] = z3.MkEq(BPGen[j], RZero);
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion

                #region COST of GENERATION
                {
                    ArithExpr[] Exprs = new ArithExpr[nGBuses];
                    k = 0;
                    for (j = 1; j <= nBuses; j++)
                    {
                        if (mBG[j])
                            Exprs[k++] = z3.MkAdd(z3.MkReal(Convert.ToString(costCoef[j, 0])),
                                z3.MkMul(z3.MkReal(Convert.ToString(costCoef[j, 1] / scalling)), BPGen[j]));
                    }

                    BoolExpr expr = z3.MkEq(PGenCOST, z3.MkAdd(Exprs));
                    par.Assert(expr);
                    par.Assert(z3.MkLe(PGenCOST, z3.MkReal(Convert.ToString(ThPGenCost))));
                }
                #endregion

                #region [Added]  DELTA GENERATION = NEW GEN - PRE ATTACK GEN
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        if (mBG[j])
                            Exprs[j - 1] = z3.MkEq(DelGEN[j], z3.MkSub(BPGen[j], z3.MkReal(Convert.ToString(generation[j]))));
                        else
                            Exprs[j - 1] = z3.MkEq(DelGEN[j], RZero);
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion

                #region Sum of ATTACK DEMAND = Sum of GENERATION
                {
                    RealExpr[] Exprs = new RealExpr[nGBuses];
                    k = 0;

                    for (j = 1; j <= nBuses; j++)
                    {
                        if (mBG[j])
                            Exprs[k++] = DelGEN[j];
                    }

                    par.Assert(z3.MkEq(TDelGEN, z3.MkAdd(Exprs)));

                    BoolExpr Expr = z3.MkAnd(z3.MkGe(TDelGEN, TDelBP), z3.MkLe(TDelGEN, z3.MkMul(TDelBP,
                        z3.MkReal(Convert.ToString((100.0 + THRESHOLD_DIFF) / 100.0)))));
                    par.Assert(Expr);
                }
                #endregion

                //Bus Consumption and line flow
                #region [Added] Bus Consumptions Attack and Real
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = z3.MkAnd(z3.MkEq(DelBC_ATTACK[j], z3.MkSub(DelGEN[j], DelBP[j])), z3.MkEq(DelBC_REAL[j], DelGEN[j]));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion

                #region [Added] Line Flow under Real Data PL = PBC x SF
                {
                    for (i = 1; i <= nLines; i++)
                    {
                        ArithExpr[] Exprs = new ArithExpr[nBuses - 1];
                        for (j = 2; j <= nBuses; j++)
                        {
                            Exprs[j - 2] = z3.MkMul(DelBC_REAL[j], z3.MkReal(Convert.ToString(SF[i - 1, j - 2])));
                        }

                        BoolExpr Expr = z3.MkEq(DelFPL_REAL[i], z3.MkAdd(Exprs));
                        par.Assert(Expr);
                        //tw.WriteLine("(assert {0})", Expr.ToString());
                    }
                }
                #endregion
                #region [Added] FLP_REAL LINE POWER FLOW  
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkEq(FLP_REAL[i], z3.MkAdd(DelFPL_REAL[i], z3.MkReal(Convert.ToString(preattackFlow[i]))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion
                #region [Added] BLP_REAL  = 0 - FLP_REAL
                {
                    for (i = 1; i <= nLines; i++)
                    {
                        BoolExpr Expr = z3.MkEq(BLP_REAL[i], z3.MkSub(RZero, FLP_REAL[i]));
                        par.Assert(Expr);
                    }
                }
                #endregion


                #region [Added] Line Flow under Attack Data PL = PBC x SF
                {
                    for (i = 1; i <= nLines; i++)
                    {
                        ArithExpr[] Exprs = new ArithExpr[nBuses - 1];
                        for (j = 2; j <= nBuses; j++)
                        {
                            Exprs[j - 2] = z3.MkMul(DelBC_ATTACK[j], z3.MkReal(Convert.ToString(SF[i - 1, j - 2])));
                        }

                        BoolExpr Expr = z3.MkEq(DelFPL_ATTACK[i], z3.MkAdd(Exprs));
                        par.Assert(Expr);
                        //tw.WriteLine("(assert {0})", Expr.ToString());
                    }
                }
                #endregion
                #region [Added] FLP_ATTACK LINE POWER FLOW  
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkEq(FLP_ATTACK[i], z3.MkAdd(DelFPL_ATTACK[i], z3.MkReal(Convert.ToString(preattackFlow[i]))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                #endregion
                #region [Added] BLP_ATTACK  = 0 - FLP_ATTACK
                {
                    for (i = 1; i <= nLines; i++)
                    {
                        BoolExpr Expr = z3.MkEq(BLP_ATTACK[i], z3.MkSub(RZero, FLP_ATTACK[i]));
                        par.Assert(Expr);
                    }
                }
                #endregion


                //*************POWER FLOW BASED ON ATTACK DATA***********
                //****************** Commented ************************** 
                #region [commented] FLP_ATTACK and BLP_ATTACK (using THETA * admittance)
                /*
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        // Based on real topology
                        Exprs[i - 1] = z3.MkEq(FLP_ATTACK[i],
                            z3.MkMul(z3.MkSub(THETA_ATTACK[powerLine[i, 0]], THETA_ATTACK[powerLine[i, 1]]),
                                z3.MkReal(Convert.ToString(lineAdmittance[i]))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
               */

                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkEq(BLP_ATTACK[i], z3.MkSub(RZero, FLP_ATTACK[i]));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }

                // The phase angle of the reference bus is zero
                {
                    BoolExpr Expr = z3.MkEq(THETA_ATTACK[refBus], z3.MkReal(0));
                    par.Assert(Expr);
                }
                #endregion
                #region [commented] Bus Consumption (LOAD-GENRATION) with ATTACK LOAD  [????]
                /*
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {

                        Exprs[j - 1] = z3.MkEq(BPow_ATTACK[j], z3.MkSub(BPGen[j], BDem_ATTACK[j])); // L_a calculation
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                */
                #endregion
                #region [commented] BUS CONSUMPTION FOR ATTACK DEMAND (SUM of LINE FLOW TOWARD/FROM EACH BUS)
                /*
                 {
                    BoolExpr[] Exprs2 = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        // If a bus is connected with NO bus, then the THETA will be zero and 
                        // the power consumption at this bus will depend on its load only
                        if (connected[j, 0] == 0)
                        {
                            Exprs2[j - 1] = z3.MkEq(THETA_ATTACK[j], RZero);
                        }

                        else
                        {
                            ArithExpr[] Exprs = new ArithExpr[connected[j, 0]];
                            for (i = 1; i <= connected[j, 0]; i++)
                            {
                                k = mConnect[j, connected[j, i]];

                                if (j == powerLine[k, 0])
                                    Exprs[i - 1] = FLP_ATTACK[k];
                                else
                                    Exprs[i - 1] = BLP_ATTACK[k];
                            }
                            Exprs2[j - 1] = z3.MkEq(BPow_ATTACK[j], z3.MkAdd(Exprs));
                        }
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs2);
                    par.Assert(Expr);
                }
                #endregion

                #region FLP_ATTACK and BLP_ATTACK CAPACITY LIMIT (LINE FLOW) 
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];

                    for (i = 1; i <= nLines; i++)
                    {
                        double minPL = (-1) * maxPL[i];
                        Exprs[i - 1] = z3.MkAnd(z3.MkGe(FLP_ATTACK[i], z3.MkReal(Convert.ToString(minPL))),
                            z3.MkLe(FLP_ATTACK[i], z3.MkReal(Convert.ToString(maxPL[i]))));
                    }
                    BoolExpr Exprx = z3.MkAnd(Exprs);
                    par.Assert(Exprx);
                }
                */
                #endregion
                //*******************************************************//

                #region(N - 1) LINE CONTINGENCY FLOW FOR ATTACK DATA
                {
                    for (k = 1; k <= nLines; k++)
                    {
                        for (l = 1; l <= nLines; l++)
                        {
                            //if (l != k)
                            {
                                //Console.WriteLine("{0}", LODF[k - 1, l - 1]);
                                RealExpr Delta_FLP = (RealExpr)z3.MkMul(FLP_ATTACK[k], z3.MkReal(Convert.ToString(LODF[k - 1, l - 1])));
                                RealExpr Changed_FLP = (RealExpr)z3.MkAdd(FLP_ATTACK[l], Delta_FLP);
                                par.Assert(z3.MkEq(FLP_CON_ATTACK[k, l], Changed_FLP));
                            }
                            /*
                            else
                            {
                                par.Assert(z3.MkEq(FLP_CON_ATTACK[k, l], RZero));
                            }*/
                        }
                    }
                    for (k = 1; k <= nLines; k++)
                    {
                        for (l = 1; l <= nLines; l++)
                        {
                            BoolExpr Expr = z3.MkEq(BLP_CON_ATTACK[k, l], z3.MkSub(RZero, FLP_CON_ATTACK[k, l]));
                            par.Assert(Expr);
                        }
                    }
                }
                #endregion

                #region CONTINGENCY FLOW MAX LIMIT FOR ATTACK DATA (should be in LIMIT as it is in SCOPF)
                // If after contingency each line is in LIMIT or NOT??
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        BoolExpr[] OneLineOut = new BoolExpr[nLines];
                        for (j = 1; j <= nLines; j++)
                        {
                            double minPL = (-1) * maxPL[j];

                            OneLineOut[j - 1] = z3.MkAnd(z3.MkGe(FLP_CON_ATTACK[i, j], z3.MkReal(Convert.ToString(minPL))),
                                z3.MkLe(FLP_CON_ATTACK[i, j], z3.MkReal(Convert.ToString(maxPL[j]))));
                        }
                        Exprs[i - 1] = z3.MkAnd(OneLineOut);
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }

                #endregion

                //POWER FLOW BASED ON REAL DATA

                #region [commented] FLP_REAL and BLP_REAL (using THETA * admittance)
                /*
                {
                    
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Console.WriteLine("{0}--{1}", powerLine[i, 0], powerLine[i, 1]);

                        // Based on real topology
                        Exprs[i - 1] = z3.MkEq(FLP_REAL[i],
                            z3.MkMul(z3.MkSub(THETA_REAL[powerLine[i, 0]], THETA_REAL[powerLine[i, 1]]),
                                z3.MkReal(Convert.ToString(lineAdmittance[i]))));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkEq(BLP_REAL[i], z3.MkSub(RZero, FLP_REAL[i]));
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                

                // The phase angle of the reference bus is zero
                {
                    BoolExpr Expr = z3.MkEq(THETA_REAL[refBus], z3.MkReal(0));
                    par.Assert(Expr);
                }
                */
                #endregion
                #region [commented] Bus Consumption (LOAD-GENRATION) with REAL LOAD  
                /*
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {

                        Exprs[j - 1] = z3.MkEq(BPow_REAL[j], z3.MkSub(BPGen[j], BDem_REAL[j])); // L_a calculation
                    }
                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                }
                */
                #endregion
                #region [commented] BUS CONSUMPTION FOR REAL DEMAND (SUM of LINE FLOW TOWARD/FROM EACH BUS)
                /*
                 {
                    BoolExpr[] Exprs2 = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        // If a bus is connected with NO bus, then the THETA will be zero and 
                        // the power consumption at this bus will depend on its load only
                        if (connected[j, 0] == 0)
                        {
                            Exprs2[j - 1] = z3.MkEq(THETA_REAL[j], RZero);
                        }

                        else
                        {
                            ArithExpr[] Exprs = new ArithExpr[connected[j, 0]];
                            for (i = 1; i <= connected[j, 0]; i++)
                            {
                                k = mConnect[j, connected[j, i]];

                                if (j == powerLine[k, 0])
                                    Exprs[i - 1] = FLP_REAL[k];
                                else
                                    Exprs[i - 1] = BLP_REAL[k];
                            }
                            Exprs2[j - 1] = z3.MkEq(BPow_REAL[j], z3.MkAdd(Exprs));
                        }
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs2);
                    par.Assert(Expr);
                }
                */
                #endregion

                #region FLP_REAL and BLP_REAL CAPACITY LIMIT (LINE FLOW) 
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];

                    for (i = 1; i <= nLines; i++)
                    {
                        double minPL = (-1) * maxPL[i];
                        Exprs[i - 1] = z3.MkAnd(z3.MkGe(FLP_REAL[i], z3.MkReal(Convert.ToString(minPL))),
                            z3.MkLe(FLP_REAL[i], z3.MkReal(Convert.ToString(maxPL[i]))));
                    }
                    BoolExpr Exprx = z3.MkAnd(Exprs);
                    par.Assert(Exprx);
                }
                #endregion

                // CONTINGECNY FOR REAL DATA

                #region Line Flow in (n-1) Contingency for Real Load

                for (l = 1; l <= nLines; l++)
                {
                    //if (l != targeted_line)
                    {
                        //Console.WriteLine("If: l={0}\t nLines={1}\tTargeted Line={2}", l, nLines, targeted_line);
                        RealExpr Delta_FLP = (RealExpr)z3.MkMul(FLP_REAL[targeted_line], z3.MkReal(Convert.ToString(LODF[targeted_line - 1, l - 1])));
                        RealExpr Changed_FLP = (RealExpr)z3.MkAdd(FLP_REAL[l], Delta_FLP);
                        par.Assert(z3.MkEq(Lines_Contingency_Flow_Real[l], Changed_FLP));
                    }
                    /*else
                    {
                        // Console.WriteLine("Else: l={0}\t nLines={1}\tTargeted Line={2}", l, nLines, targeted_line);
                        par.Assert(z3.MkEq(Lines_Contingency_Flow_Real[targeted_line], RZero));
                    }*/
                }


                // backward flow (commented for now)
                /*
                for (int k = 1; k <= nLines; k++)
                {
                    for (int l = 1; l <= nLines; l++)
                    {                    
                        slv.Assert(z3.MkEq(Back_Lines_Contingency_Flow_Real[k, l], z3.MkSub(Zero, Lines_Contingency_Flow_Real[k, l])));
                    }
                }
                */

                #endregion

                #region Original Flow after Contingency CAPACITY LIMIT (CASE-II, Part-overload in EACH case) 
                // If after contingency each line is in LIMIT or NOT??
                {

                    BoolExpr[] OneLineOut = new BoolExpr[nLines];
                    for (j = 1; j <= nLines; j++)
                    {
                        double MIN_OVERLOADING = 1 + (minLineOverloadAmount / 100.0);

                        //double MIN_OVERLOADING = 1.3;

                        double minPL = (-1) * maxPL[j];

                        if (targeted_line != j)
                        {
                            OneLineOut[j - 1] = z3.MkOr(z3.MkLt(Lines_Contingency_Flow_Real[j], z3.MkReal(Convert.ToString(minPL * MIN_OVERLOADING))),
                            z3.MkGt(Lines_Contingency_Flow_Real[j], z3.MkReal(Convert.ToString(maxPL[j] * MIN_OVERLOADING))));
                        }
                        else
                        {
                            OneLineOut[j - 1] = z3.MkBool(false);
                            //z3.MkNot(OneLineOut[j - 1]);
                        }
                        par.Assert(z3.MkImplies(IsOverFlowContgn[j], OneLineOut[j - 1]));
                        par.Assert(z3.MkImplies(OneLineOut[j - 1], IsOverFlowContgn[j]));

                    }
                    // Exprs[i - 1] = z3.MkOr(OneLineOut);

                    // BoolExpr Expr = z3.MkOr(Exprs);
                    //slv.Assert(Expr);

                    par.Assert(z3.MkEq(EachLineContgnCount[0], z3.MkInt(0)));

                    for (j = 1; j <= nLines; j++)
                    {
                        par.Assert(z3.MkImplies(IsOverFlowContgn[j], z3.MkEq(EachLineContgnCount[j], z3.MkInt(1))));
                        par.Assert(z3.MkImplies(z3.MkNot(IsOverFlowContgn[j]), z3.MkEq(EachLineContgnCount[j], z3.MkInt(0))));
                    }

                    IntExpr[] OneLineCountOverload = new IntExpr[nLines];
                    for (j = 1; j <= nLines; j++)
                    {
                        OneLineCountOverload[j - 1] = EachLineContgnCount[j];
                    }
                    OneSetContgnCount = (IntExpr)z3.MkAdd(OneLineCountOverload);
                    par.Assert(z3.MkGe(OneSetContgnCount, z3.MkInt(numOfLinesOverloaded)));
                }
                #endregion

                //par.Assert(z3.MkEq(CB[3],z3.MkBool(true)));

                //**********************  Ends **************************//

                #region [commented] The condition of a state being attacked (altered). (PLEASE SEE THE COMMENT BELOW)
                /*
                // IMPORTANT: If a state is altered, then the change in the state must be different from the cahnge in at least one of the neighboring buses' states.
                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        //////////////////////// Ashiq on 11/10/2015 [Start] ///////////////////////
                        // The following is not true any more:
                        // "If a state is altered, then the change in the state must be different from the cahnge in at least one of the neighboring buses' states."
                        // The commented things are uncommented and vice versa
                        Exprs[j - 1] = z3.MkEq(CX[j], z3.MkOr(z3.MkGt(DelTheta[j], z3.MkReal(0)),
                            z3.MkLt(DelTheta[j], z3.MkReal(0))));

                        //BoolExpr[] Exprs2 = new BoolExpr[connected[j, 0]];
                        //for (i = 1; i <= connected[j, 0]; i++)
                        //{
                        //    Exprs2[i - 1] = z3.MkEq(DelTheta[j], DelTheta[connected[j, i]]);
                        //}

                        //Exprs[j - 1] = z3.MkEq(CX[j], z3.MkAnd(z3.MkNot(z3.MkEq(DelTheta[j], RZero)),
                        //    z3.MkNot(z3.MkAnd(Exprs2))));
                        /////////////////////// Ashiq on 11/10/2015 [End] ////////////////////////////
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                {
                    BoolExpr[] Exprs = new BoolExpr[nCnstrOnDelTheta];
                    for (i = 1; i <= nCnstrOnDelTheta; i++)
                    {
                        if (cnstrOnCXAmt[i, 2] == 0)
                            Exprs[i - 1] = z3.MkEq(DelTheta[cnstrOnCXAmt[i, 0]], DelTheta[cnstrOnCXAmt[i, 1]]);
                        else if (cnstrOnCXAmt[i, 2] == 1)
                        {
                            // The constraints should consider whether there is an attack on both of these  states
                            Exprs[i - 1] = z3.MkNot(z3.MkEq(DelTheta[cnstrOnCXAmt[i, 0]], DelTheta[cnstrOnCXAmt[i, 1]]));
                        }
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                // We should assume a bus as a reference bus. This implies that this bus cannot be attacked.
                {
                    BoolExpr Expr = z3.MkEq(DelTheta[refBus], RZero);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                */
                #endregion

                #region The relations between the line powers, bus power consumption, and the measurements.
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        //Exprs[i - 1] = z3.MkEq(z3.MkOr(z3.MkGt(DelLP[i], z3.MkNumeral(0, realT)),
                        //        z3.MkLt(DelLP[i], z3.MkNumeral(0, realT))),
                        //    z3.MkAnd(z3.MkEq(MZ[i], CZ[i]), z3.MkEq(MZ[nLines + i], CZ[nLines + i])));
                        //Exprs[i - 1] = z3.MkImplies(z3.MkOr(z3.MkGt(DelLP[i], z3.MkNumeral(0, realT)),
                        //        z3.MkLt(DelLP[i], z3.MkNumeral(0, realT))),
                        //    z3.MkImplies(MZ[i], CZ[i]));

                        Exprs[i - 1] = z3.MkImplies(z3.MkNot(z3.MkEq(FDelLP[i], RZero)), z3.MkImplies(MZ[i], CZ[i]));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());


                    Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        //Exprs[i - 1] = z3.MkImplies(z3.MkOr(z3.MkGt(DelLP[i], z3.MkNumeral(0, realT)),
                        //        z3.MkLt(DelLP[i], z3.MkNumeral(0, realT))),
                        //    z3.MkImplies(MZ[nLines + i], CZ[nLines + i]));                            
                        Exprs[i - 1] = z3.MkImplies(z3.MkNot(z3.MkEq(BDelLP[i], RZero)),
                            z3.MkImplies(MZ[nLines + i], CZ[nLines + i]));
                    }

                    Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());


                    Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(CZ[i], z3.MkNot(z3.MkEq(FDelLP[i], RZero)));
                    }

                    Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());


                    Exprs = new BoolExpr[nLines];
                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(CZ[nLines + i], z3.MkNot(z3.MkEq(BDelLP[i], RZero)));
                    }

                    Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                {
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        //Exprs[j - 1] = z3.MkEq(z3.MkOr(z3.MkGt(DelBP[j], z3.MkNumeral(Convert.ToString(0), realT)),
                        //        z3.MkLt(DelBP[j], z3.MkNumeral(Convert.ToString(0), realT))),
                        //    z3.MkEq(MZ[2 * nLines + j], CZ[2 * nLines + j]));
                        Exprs[j - 1] = z3.MkImplies(z3.MkNot(z3.MkEq(DelBP[j], RZero)),
                            z3.MkImplies(MZ[2 * nLines + j], CZ[2 * nLines + j]));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());


                    Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = z3.MkImplies(CZ[2 * nLines + j], z3.MkNot(z3.MkEq(DelBP[j], RZero)));
                    }

                    Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                #endregion

                #region The attacker only can attack those measurements if the attacker has necessary knowledge.
                {
                    BoolExpr[] Exprs = new BoolExpr[nLines];

                    for (i = 1; i <= nLines; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(z3.MkOr(CZ[i], CZ[nLines + i]), BD[i]);
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                #endregion

                #region If a measurement is chosen for false data injection, then the following must be true:
                // It is recorded (measured), the attacker has the capability, and the measurements is not secured.                    
                {
                    BoolExpr[] Exprs = new BoolExpr[nMeasurements];
                    for (i = 1; i <= nMeasurements; i++)
                    {
                        Exprs[i - 1] = z3.MkImplies(CZ[i], z3.MkAnd(new BoolExpr[] { MZ[i], AZ[i], z3.MkNot(SZ[i]) }));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                #endregion

                #region If the measurements at which substations (buses) are required to be compromised.
                {
                    // Relation be//tweeen a measurement change with compromising a bus
                    BoolExpr[] Exprs = new BoolExpr[nMeasurements];
                    for (i = 1; i <= nLines; i++)
                    {
                        int fBus = powerLine[i, 0];
                        int tBus = powerLine[i, 1];
                        Exprs[i - 1] = z3.MkImplies(CZ[i], CB[fBus]);
                        Exprs[nLines + i - 1] = z3.MkImplies(CZ[nLines + i], CB[tBus]);
                    }

                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[2 * nLines + j - 1] = z3.MkImplies(CZ[2 * nLines + j], CB[j]);
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }

                {
                    // Relation be//tweeen compromising a bus with associated measurement change
                    BoolExpr[] Exprs = new BoolExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        BoolExpr[] Exprs2 = new BoolExpr[connected[j, 0] + 1];
                        for (k = 1; k <= connected[j, 0]; k++)
                        {
                            i = mConnect[j, connected[j, k]];   // Line No
                            int fBus = powerLine[i, 0];
                            int tBus = powerLine[i, 1];
                            if (fBus == j)
                                Exprs2[k - 1] = CZ[i];
                            else
                                Exprs2[k - 1] = CZ[nLines + i];
                        }

                        Exprs2[k - 1] = CZ[2 * nLines + j];
                        Exprs[j - 1] = z3.MkImplies(CB[j], z3.MkOr(Exprs2));
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());
                }
                #endregion

                #region Resource Limitation Constraints
                {
                    // The Number of Measurements to be attacked should be within a Limited Numbers
                    BoolExpr[] Exprs = new BoolExpr[nMeasurements];
                    IntExpr[] Exprs2 = new IntExpr[nMeasurements];
                    for (i = 1; i <= nMeasurements; i++)
                    {
                        Exprs[i - 1] = z3.MkAnd(z3.MkImplies(CZ[i], (z3.MkEq(CZ2[i], z3.MkNumeral(1, intT)))),
                            z3.MkImplies(z3.MkNot(CZ[i]), (z3.MkEq(CZ2[i], z3.MkNumeral(0, intT)))));
                        Exprs2[i - 1] = CZ2[i];
                    }

                    BoolExpr Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());

                    BoolExpr Expr2 = z3.MkLe(z3.MkAdd(Exprs2), z3.MkInt(thCZ));
                    par.Assert(Expr2);
                    //tw.WriteLine("(assert {0})", Expr2.ToString());


                    // The Number of Attackable States should be within a minimum and maximum range
                    Exprs = new BoolExpr[nBuses];
                    Exprs2 = new IntExpr[nBuses];
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = z3.MkAnd(z3.MkImplies(CX[j], (z3.MkEq(CX2[j], z3.MkNumeral(1, intT)))),
                                z3.MkImplies(z3.MkNot(CX[j]), (z3.MkEq(CX2[j], z3.MkNumeral(0, intT)))));
                        Exprs2[j - 1] = CX2[j];
                    }

                    Expr = z3.MkAnd(Exprs);
                    //par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());

                    Expr2 = z3.MkAnd(z3.MkGe(z3.MkAdd(Exprs2), z3.MkInt(nStatesToAttack)), z3.MkLe(z3.MkAdd(Exprs2), z3.MkInt(thCX)));
                    //par.Assert(Expr2);
                    //tw.WriteLine("(assert {0})", Expr2.ToString());


                    // The Number of Buses (Substations) to be attacked should be within a Limited Numbers                        
                    for (j = 1; j <= nBuses; j++)
                    {
                        Exprs[j - 1] = z3.MkAnd(z3.MkImplies(CB[j], (z3.MkEq(CB2[j], z3.MkNumeral(1, intT)))),
                                z3.MkImplies(z3.MkNot(CB[j]), (z3.MkEq(CB2[j], z3.MkNumeral(0, intT)))));
                        Exprs2[j - 1] = CB2[j];
                    }

                    Expr = z3.MkAnd(Exprs);
                    par.Assert(Expr);
                    //tw.WriteLine("(assert {0})", Expr.ToString());

                    Expr2 = z3.MkLe(z3.MkAdd(Exprs2), z3.MkInt(thCB));
                    par.Assert(Expr2);
                    //tw.WriteLine("(assert {0})", Expr2.ToString());
                }
                #endregion

                #region Preselected Buses to attack 
                int flag_count;
                //Console.WriteLine("Targeted Bus: ");
                for (i = 1; i <= nBuses; i++)
                {

                    flag_count = 0;
                    for (j = 0; j < NumAttBus; j++)
                    {

                        if (i == AttBusList[Bus_count, j])
                        {
                            flag_count = 1;
                            break;
                        }


                    }
                    
                    //Console.WriteLine();
                    if (flag_count == 1)
                    {
                        //Console.Write("{0}, ", i);
                        //par.Assert(CB[i]);
                    }
                    else
                    {
                        //Console.WriteLine("Safe Bus Bus: {0}", i);
                        //par.Assert(z3.MkNot(CB[i]));
                    }

                }

                #endregion

            }
            #endregion

        }

        // The model and corresponding output
        int Enumerate(int Line_count, int Bus_count)
        {
            targeted_line = AttLinesList[Line_count];

            Model model = null;

            int i;

            tw2 = new StreamWriter(String.Format("Attack_Vectors_Details_{0}_{1}_{2}_{3}_{4}_{5}.txt",
                NBUSES, NLINES, NumAttBus, PercentOfDelta, minLineOverloadAmount, nPercContgnOverloadLine), true);
            //tw3 = new StreamWriter(String.Format("Attack_Vectors_Summary_{0}_{1}_{2}_{3}_{4}_{5}.txt", NBUSES, NLINES, NumAttBus, PercentOfDelta, minLineOverloadAmount, nPercContgnOverloadLine), true);

            if (Bus_count == 0)
            {
                tw2.WriteLine("*********************************  Targeted Line:  {0}  ***********************************", targeted_line);

            }

            tw2.Write("Attack Bus Set:\t");
            for (i = 0; i < NumAttBus; i++)
            {
                tw2.Write("{0}\t", AttBusList[Bus_count, i]);
            }

            // Console.Write("Attack Bus Set:\t");
            for (i = 0; i < NumAttBus; i++)
            {
                //Console.Write("{0}\t", AttBusList[Bus_count, i]);
            }

            int numSolution = 0;
            tw2.WriteLine();

            //Stopwatch stopWatch_2 = new Stopwatch();
            //stopWatch_2.Start();
            while (par.Check() == Status.SATISFIABLE)
            {


                //stopWatch_2.Stop();
                //tw2.WriteLine("Required time -{0}: {1}\n", numSolution, stopWatch_2.Elapsed.TotalSeconds);
                Console.WriteLine("We have a solution--{0}", numSolution);
                //Console.WriteLine("Required time -{0}: {1}", numSolution, stopWatch_2.Elapsed.TotalSeconds);
                //stopWatch_2.Start();
                numSolution++;
                model = par.Model;

                BoolExpr[] args = new BoolExpr[nBuses];
                int nArgs = 0;
                tw2.WriteLine("The buses at which one or more measurements are required to alter:");
                for (i = 1; i <= nBuses; i++)
                {
                    if (Convert.ToBoolean(model.Eval(CB[i]).ToString()))
                    {
                        tw2.Write("{0} ", i);
                        //Console.WriteLine("{0} ", i);
                        args[nArgs++] = CB[i];
                    }
                    else
                        args[nArgs++] = z3.MkNot(CB[i]);
                }
                tw2.WriteLine();

                //******************************
                tw2.WriteLine("Measurement need to be compromised:");
                for (i = 1; i < nMeasurements; i++)
                {
                    if (Convert.ToBoolean(model.Eval(CZ[i]).ToString()))
                    {
                        tw2.Write("{0}, ", i);
                    }
                }


                tw2.WriteLine();
                tw2.WriteLine("The attacked measurement at buses : Delta BP");
                //Console.WriteLine("The buses at which one or more measurements are required to alter:");

                for (i = 1; i <= nBuses; i++)
                {
                    if (Convert.ToBoolean(model.Eval(CB[i]).ToString()))
                    {
                        //Console.WriteLine("{0} ", i);
                        //tw2.Write("{0} ", i);
                        tw2.Write("Bus {0}: {1}\n", i, Math.Round(LargeNumberDivide(model.Eval(DelBP[i]).ToString()), 5));

                        //args_CB[nArgs_CB++] = CB[i];
                    }
                    //else
                    // args_CB[nArgs_CB++] = z3.MkNot(CB[i]);
                }
                tw2.WriteLine();

                //*****************************

                tw2.WriteLine("GENERATION DATA");
                for (i = 1; i <= nBuses; i++)
                {
                    if (mBG[i])
                    {
                        //Console.WriteLine("Bus {0} ", i + " generation: " + Math.Round(ToDouble(model.Eval(BPG[i]).ToString()), 5));
                        tw2.WriteLine("Bus {0} ", i + " generation: " + Math.Round(LargeNumberDivide(model.Eval(BPGen[i]).ToString()), 5));
                    }

                }

                //Console.WriteLine();
                tw2.WriteLine();

                tw2.WriteLine("DelGEN");
                for (i = 1; i <= nBuses; i++)
                {
                    //Console.WriteLine("Bus {0} ", i + " generation: " + Math.Round(ToDouble(model.Eval(BPG[i]).ToString()), 5));
                    tw2.WriteLine("Bus {0} ", i + " DelGEN: " + Math.Round(LargeNumberDivide(model.Eval(DelGEN[i]).ToString()), 5));

                }
                tw2.WriteLine();

                tw2.WriteLine("DelBC_ATTACK");
                for (i = 1; i <= nBuses; i++)
                {
                    //Console.WriteLine("Bus {0} ", i + " generation: " + Math.Round(ToDouble(model.Eval(BPG[i]).ToString()), 5));
                    tw2.WriteLine("Bus {0} ", i + " DelBC_ATTACK: " + Math.Round(LargeNumberDivide(model.Eval(DelBC_ATTACK[i]).ToString()), 5));

                }
                tw2.WriteLine();

                tw2.WriteLine("DelBC_REAL");
                for (i = 1; i <= nBuses; i++)
                {
                    //Console.WriteLine("Bus {0} ", i + " generation: " + Math.Round(ToDouble(model.Eval(BPG[i]).ToString()), 5));
                    tw2.WriteLine("Bus {0} ", i + " DelBC_ATTACK: " + Math.Round(LargeNumberDivide(model.Eval(DelBC_REAL[i]).ToString()), 5));

                }

                //Console.WriteLine();
                tw2.WriteLine();


                //Console.WriteLine();
                tw2.WriteLine();

                tw2.WriteLine("FLP_REAL with Original Load");

                for (i = 1; i <= nLines; i++)
                {

                    //Console.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(FLP_REAL[i]).ToString()), 5));
                    tw2.WriteLine("flow in line {0} ", i + ": " + Math.Round(LargeNumberDivide(model.Eval(FLP_REAL[i]).ToString()), 3) / scalling);
                }
                tw2.WriteLine();

                tw2.WriteLine("FLP_ATTACK with Attack Load");

                for (i = 1; i <= nLines; i++)
                {

                    //Console.WriteLine("flow in line {0} ", i + ": " + Math.Round(ToDouble(model.Eval(FLP_REAL[i]).ToString()), 5));
                    tw2.WriteLine("flow in line {0} ", i + ": " + Math.Round(LargeNumberDivide(model.Eval(FLP_ATTACK[i]).ToString()), 3) / scalling);
                }

                //Console.WriteLine();
                tw2.WriteLine();



                tw2.WriteLine("REAL FLOW after Contingency");


                //Console.WriteLine("Line {0} out: ", targeted_line);
                tw2.WriteLine("Line {0} out: ", targeted_line);
                for (int j = 1; j <= nLines; j++)
                {
                    //Console.WriteLine("flow in line {0}", j + ": " + Math.Round(ToDouble(model.Eval(Lines_Contingency_Flow_Real[j]).ToString()), 5));
                    tw2.WriteLine("flow in line {0} \t\t\tRated Capacity {2}\t Overloaded ? : {1}", j + ": " +
                        Math.Round(LargeNumberDivide(model.Eval(Lines_Contingency_Flow_Real[j]).ToString()), 3) / scalling, model.Eval(IsOverFlowContgn[j]), maxPL[j]);

                    // Console.WriteLine("line {0} ", j + " overflow: " + model.Eval(IsOverFlowContgn[i, j]).ToString());

                }
                //Console.WriteLine("Contingency OVERLOADED Lines in this Set: {0}", (model.Eval(OneSetContgnCount).ToString()));
                tw2.WriteLine("Contingency OVERLOADED Lines in this Set: {0}", (model.Eval(OneSetContgnCount).ToString()));

                //Console.WriteLine("SCOPF Cost found: " + Math.Round(ToDouble(model.Eval(Cost).ToString())));
                tw2.WriteLine("SCOPF Cost found: " + Math.Round(LargeNumberDivide(model.Eval(PGenCOST).ToString())));

                //*****************************


                //*******************************

                model.Dispose();

                par.Assert(z3.MkNot(z3.MkAnd(args)));

                if (numSolution > 0)
                    break;

            }

            tw2.WriteLine();
            tw2.WriteLine("{0} {1} {2}", thCZ, thCB, numSolution);
            tw2.Close();

            return numSolution;
        }
        void Model()
        {

            Dictionary<string, string> cfg = new Dictionary<string, string>() {
                { "MODEL", "true"},
                { "TIMEOUT", TIME_OUT}
            };

            try
            {


                //z3.OpenLog("Managemnt_Log2.txt");            
                //Random rand = new Random();

                z3 = new Context(cfg);
                par = z3.MkSolver();
                ReadInput();
                //ReadBinDB();


                int redFlag;
                int newlineFlag;

                for (int Line_count = 0; Line_count < AttLinesList.Length; Line_count++)
                {
                    newlineFlag = 1;
                    Console.WriteLine("Line: {0}", AttLinesList[Line_count]);

                    for (int Bus_count = 0; Bus_count < TotalBusCombination; Bus_count++)
                    {
                        //Console.WriteLine("Bus: {0}", Bus_count);

                        int l = 0, k = 0;

                        redFlag = 0;

                        /////////////// Checking in the bin Dataset
                        //
                        //Console.WriteLine("Attack Bus List Data Base");

                        for (int j = 0; j < NumAttBus; j++)
                        {
                            // Console.Write("{0} ", AttBusList[Bus_count, j]);
                        }

                        //Console.Write("\n");
                        ////////////////////////////////////////////////////
                        ///
                        //Console.WriteLine("TotalBinCase : {0}", TotalBinCase);


                        for (int i = 0; i < TotalBinCase; i++)
                        {
                            ///Console.WriteLine("Binary Data Base");
                            for (int j = 0; j < 16; j++)
                            {
                                //Console.Write("{0} ", BinDB[i, j]);
                            }

                            k = i;
                            //int check = 1;


                            int label = BinDB[i, NBUSES + 1];
                            //Console.WriteLine("{0}", label);

                            if (i == TotalBinCase - 1)

                                for (int j = 0; j < NumAttBus; j++)
                                {
                                    //Console.Write("{0} ", BinDB[i, AttBusList[Bus_count, j]]);
                                }

                            //Console.WriteLine("Line Count");
                            if (BinDB[i, 0] == AttLinesList[Line_count])
                            {

                                //Console.WriteLine("Line Count");

                                int j = 0;

                                for (j = 0; j < NumAttBus; j++)
                                {
                                    l = j;
                                    //Console.Write(BinDB[i, AttBusList[Bus_count, j]]);
                                    //Console.WriteLine(i);
                                    if (BinDB[i, AttBusList[Bus_count, j]] != 1)
                                    {
                                        //Console.Write("\ti={0}, \tj={1}",i, j);
                                        break;
                                    }
                                    //Console.WriteLine("");

                                    //Console.Write("{0}\t", AttBusList[Bus_count, i]);
                                }

                                //Console.WriteLine("Bus_count={0}, i={1} and j= {2}", Bus_count,i, j);

                                if (j == NumAttBus && label == targetedCase)
                                {
                                    //Console.WriteLine("label:  {0}", label);
                                    redFlag = 1;
                                    //Console.WriteLine("redFlag:  {0} Breaking\n", redFlag);
                                    break;

                                }



                            }

                        }
                        ///////////////////////////////////////////////////////////////
                        ///
                        //Console.WriteLine("redFlag:  {0}", redFlag);

                        if (redFlag == 1)
                        {
                            //Console.WriteLine("Already checked! i={0}", k);
                            continue;
                        }



                        tw3 = new StreamWriter(String.Format("Attack_Vectors_Summary_{0}_{1}_{2}_{3}_{4}_{5}.txt",
                                NBUSES, NLINES, NumAttBus, PercentOfDelta, minLineOverloadAmount, nPercContgnOverloadLine), true);

                        if (newlineFlag == 1)
                        {
                            newlineFlag = 0;
                            tw3.WriteLine("***********************************  Targeted Line:  {0}  *************************************", AttLinesList[Line_count]);
                            tw3.WriteLine();
                            //Console.WriteLine("*****************  Targeted Line:  {0}  ****************", AttLinesList[Line_count]);
                        }

                        tw3.Write("Attack Bus Set:\t");

                        //Console.Write("Attack Bus Set:\t");

                        for (int ii = 0; ii < NumAttBus; ii++)
                        {
                            tw3.Write("{0}\t", AttBusList[Bus_count, ii]);
                            //Console.Write("{0}\t", AttBusList[Bus_count, i]);
                        }
                        Stopwatch stopWatch = new Stopwatch();
                        
                        stopWatch.Start();
                        Formalize(Line_count, Bus_count);
                        int ns = Enumerate(Line_count, Bus_count);
                        stopWatch.Stop();

                        tw3.Write("\t\tNumber of Solutions: {0}", ns);

                        if (ns > 0)
                        {
                            Console.WriteLine("Number of Solutions: {0}", ns);
                            Console.WriteLine("Required time: {0}", stopWatch.Elapsed.TotalSeconds);
                        }
                        tw3.WriteLine("\t\tRequired time: {0}", stopWatch.Elapsed.TotalSeconds);
                       
                        if (Bus_count == (NumAttBus))
                        {
                            tw3.WriteLine();
                            tw3.WriteLine();
                        }
                        tw3.Close();
                        par.Dispose();
                        z3.Dispose();

                        z3 = new Context(cfg);
                        par = z3.MkSolver();
                        ReadInput();
                    }
                }

            }
            catch (Exception exp)
            {
                Console.WriteLine(exp.ToString());
                par.Dispose();
                z3.Dispose();
                Environment.Exit(0);
            }

        }




        // Main Function
        static void Main(string[] args)
        {


            DateTime now = DateTime.Now;
            Console.WriteLine("************  FDI on SCOPF  **************");
            //Console.WriteLine("Number Buses: {0} Number of Lines: {1}", NBUSES, NLINES);
            Console.WriteLine(now);
            string path = Directory.GetCurrentDirectory();
            Console.WriteLine("Running from:\n{0}", path);
            Estimation est = new Estimation();
            //Stopwatch stopWatch = new Stopwatch();
            //stopWatch.Start();


            est.Model();


            //stopWatch.Stop();

            //Console.WriteLine("Required time: {0}", stopWatch.Elapsed.TotalSeconds);


        }
    }
}
