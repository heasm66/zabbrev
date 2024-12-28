//#define STOPWATCH       // Define this if you want the --stopwatches option
//#define _IN_DEVELOPMENT   // Set this to false before release

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Globalization;
using System.IO;
using System.Linq;
using System.Reflection;
using System.Threading;

//Copyright (C) 2021, 2024 Henrik Åsman
//You can redistribute and/or modify this file under the terms of the
//GNU General Public License as published by the Free Software
//Foundation, either version 3 of the License, or (at your option) any
//later version.
//This file is distributed in the hope that it will be useful, but
//WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
//General Public License for more details.
//You should have received a copy of the GNU General Public License
//along with this file. If not, see <https://www.gnu.org/licenses/>."

// TODO:
//   * OK: Convert to C# (converter.telerik.com)
//   * OK: When C#, use Span instead of Array
//   * OK: Add output option to UnZil for a gametext.txt-file
//   * Optimization for pass 2, use suffix array?
//   * Find better algorithm for viable patterns to test in pass 2
//   * Refactoring tip: suggest beginning or end of text globals (".^" = PERIOD-CR)
//   * Switch to export ZIL alphabet in ZAP-format (so a bat-script can pipe it in automatically)
//   * OK: Warning that custom alphabet isn't defined for versions 1-4.
//   * Option to limit length of abbreviations (Inform6 have a limit of 64 characters).
//   * OK: Warning that abbreviations exceed limit for Inform6 targets
//       - Issue a warning when one or more abbreviations exceed 64 characters and suggest refactoring code.
//   * OK: Craverly Heights, encoding error
//   * OK: New switch -x that sets compression level. x2 is default.
//       -x0 Fastest Pick abbreviations according to highest score with R.A. Wagner's "optimal Parse" method.
//       -x1 Fast    x0 + Try adding and removing initial and trailing space to abbreviations adjusting for z-chars rounding.
//       -x2 Normal  x1 + Try 10.000 discarded variants of abbreviations to see if they adjust better for z-chars rounding.
//       -x3 Maximum x2 + Try 1.000 discarded abbreviations as all possible replacements to get best adjustment for z-chars rounding. 

// Changelog:
// 0.8  2022-01-15 Visual Studio 2019, NET5.0
// 0.9  2023-08-11 Visual Studio 2022, NET7 (3x faster then earlier version)
//                 Using new features when publishing
//                 Small optimizations
// 0.10 2024-01-10 Visual Studio 2022, NET8
//                 Using Suffix Array for optimizations (2x faster then earlier version)
//                 New output/statistics
// 0.11 2024-xx-xx Fix encoding error when building suffix array
//                 Multiple passes when adding/removing spaces
//                 Organize different compression options into -x[0-3], compression level
//                 Added test with one or two initial/trailing characters removed
//                 Use Inform-standard replacement chars for quote, space and CR
//                 Use z-code padding information (if available) from gametext.txt created by unz
//                 Modified statistics
//                 Warnings when abbreviation exceeds 64 characters for Inform6 or custom alphabet is created for v1-4.
//                 Stopwatches (optional)
//                 Visual Studio 2022, NET9 
//                 VB.NET --> C#
//                 ZAbbrevMaker --> ZAbbrev
//                 Replace StringBuilder objects with AsSpan()
//                 zabbrev without argas and no files to process equals -h

namespace zabbrev
{
    internal static class Program
    {
        public const int NUMBER_OF_ABBREVIATIONS = 96;
        public const char SPACE_REPLACEMENT = ' ';
        public const char QUOTE_REPLACEMENT = '~';
        public const char LF_REPLACEMENT = '^';
        public const int ABBREVIATION_REF_COST = 2; // An abbreviation reference Is 2 characters,
        public const int NUMBER_OF_PASSES_DEFAULT = 10000;
        public const int NUMBER_OF_DEEP_PASSES_DEFAULT = 1000;
        public const int CUTOFF_LONG_PATTERN = 20;

        private static readonly string defaultA0 = "abcdefghijklmnopqrstuvwxyz";
        private static readonly string defaultA1 = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        private static readonly string defaultA2 = "0123456789.,!?_#'/\\-:()"; // 3 slots are reserved for an escape char, newline and doublequote
        private static bool customAlphabet = false;
        private static string alphabet0 = defaultA0;
        private static string alphabet1 = defaultA1;
        private static string alphabet2 = defaultA2;
        private static readonly HashSet<char> alphabet0Hash = [];
        private static readonly HashSet<char> alphabet1And2Hash = [];
        private static bool OutputRedirected = false;
        private static int zVersion = 0;
        private static bool tryAutoDetectZVersion = false;
        private static int NumberOfAbbrevs { get; set; } = NUMBER_OF_ABBREVIATIONS;
        private static System.Text.Encoding TextEncoding { get; set; } = null;

        private static string infodumpFilename = "";
        private static string txdFilename = "";

        private static bool verbose = false;
        private static bool onlyRefactor = false;
        private static int compressionLevel = 2;
        private static readonly List<int> routineSize = [];
        private static int latestTotalPadding = 0;
        private static int outputFormat = 0;
        private static DateTime buildDateTimeLocal;
        private static string buildTimestamp;
        private static int numberOfPasses = NUMBER_OF_PASSES_DEFAULT;
        private static int numberOfDeepPasses = NUMBER_OF_DEEP_PASSES_DEFAULT;

#if STOPWATCH
        private static bool stopwatches = false;
        private static int callCount = 0;
#endif

#if STOPWATCH
        private static readonly Stopwatch sw1 = new();
        private static readonly Stopwatch sw2 = new();
        private static readonly Stopwatch sw3 = new();
        private static readonly Stopwatch sw4 = new();
        private static readonly Stopwatch sw5 = new();
#endif
        public static void Main(string[] args)
        {
            bool forceRoundingTo3 = false;
            bool printDebug = false;
            bool throwBackLowscorers = false;
            bool inform6StyleText = false;
            string gameDirectory = Environment.CurrentDirectory;

            // Get date of build in format "1st January 2025"
            buildDateTimeLocal = GetBuildDateUtc(Assembly.GetExecutingAssembly()).ToLocalTime();
            buildTimestamp = buildDateTimeLocal.ToString("dxx xMM yyyy");
            buildTimestamp = buildTimestamp.Replace("x01", "January");
            buildTimestamp = buildTimestamp.Replace("x02", "February");
            buildTimestamp = buildTimestamp.Replace("x03", "March");
            buildTimestamp = buildTimestamp.Replace("x04", "April");
            buildTimestamp = buildTimestamp.Replace("x05", "May");
            buildTimestamp = buildTimestamp.Replace("x06", "June");
            buildTimestamp = buildTimestamp.Replace("x07", "July");
            buildTimestamp = buildTimestamp.Replace("x08", "August");
            buildTimestamp = buildTimestamp.Replace("x09", "September");
            buildTimestamp = buildTimestamp.Replace("x10", "October");
            buildTimestamp = buildTimestamp.Replace("x11", "November");
            buildTimestamp = buildTimestamp.Replace("x12", "December");
            switch (buildTimestamp[..2]){
                case "1x": case "21":case "31" : buildTimestamp = buildTimestamp.Replace("xx", "st"); break;
                case "2x": case "22" : buildTimestamp = buildTimestamp.Replace("xx", "nd"); break;
                case "3x": case "23" : buildTimestamp = buildTimestamp.Replace("xx", "rd"); break;
                default : buildTimestamp = buildTimestamp.Replace("xx", "th"); break;
            }
#if (_IN_DEVELOPMENT == True)
            buildTimestamp += ", in development";
#endif

            // If no arguments and no files to work with, print -h
            if (args.Length == 0)
            {
                if (System.IO.File.Exists(System.IO.Path.Combine(gameDirectory, "gametext.txt")) == false && System.IO.Directory.GetFiles(gameDirectory, "*.zap").Length == 0)
                {
                    Array.Resize(ref args, 1);
                    args[0] = "-h";
                }
            }

            // Parse arguments
            for (int i = 0; i < args.Length; i++)
            {
                switch (args[i])
                {
                    case "-a":
                        customAlphabet = true;
                        break;
                    case "-a0":
                        if (i < args.Length - 1 && args[i + 1].Length == 26)
                        {
                            alphabet0 = args[i + 1];
                            i += 1;
                        }
                        else
                        {
                            Console.Error.WriteLine("WARNING: Can't use defined A0 (needs 26 characters). Using defailt instead.");
                        }
                        break;
                    case "-a1":
                        if (i < args.Length - 1 && args[i + 1].Length == 26)
                        {
                            alphabet1 = args[i + 1];
                            i += 1;
                        }
                        else
                        {
                            Console.Error.WriteLine("WARNING: Can't use defined A1 (needs 26 characters). Using defailt instead.");
                        }
                        break;
                    case "-a2":
                        if (i < args.Length - 1 && args[i + 1].Length == 23)
                        {
                            alphabet2 = args[i + 1];
                            i += 1;
                        }
                        else
                        {
                            Console.Error.WriteLine("WARNING: Can't use defined A2 (needs 23 characters). Using defailt instead.");
                        }
                        break;
                    case "-r3":
                        forceRoundingTo3 = true;
                        break;
                    case "-v":
                        verbose = true;
                        break;
                    case "--debug":
                        printDebug = true;
                        break;
                    case "-b":
                        throwBackLowscorers = true;
                        break;
                    case "-n":
                        int tempVar = 0;
                        if (i < args.Length - 1 && int.TryParse(args[i + 1], out tempVar))
                        {
                            NumberOfAbbrevs = tempVar;
                            i += 1;
                        }
                        else
                        {
                            NumberOfAbbrevs = tempVar;
                        }
                        break;
                    case "-h":
                    case "--help":
                    case "\\?":
                        Console.Error.WriteLine("ZAbbrev 0.11 ({0}) by Henrik Åsman, (c) 2021-2024",buildTimestamp);
                        Console.Error.WriteLine("Usage: zabbrev [switches] [path-to-game]");
                        Console.Error.WriteLine("Highly optimized abbreviations computed efficiently");
                        Console.Error.WriteLine();
                        Console.Error.WriteLine(" -a                 Create a tailor-made alphabet for this game and use it as basis for");
                        Console.Error.WriteLine("                    the abbreviations (z5+ only).");
                        Console.Error.WriteLine(" -a0 <string>       Define 26 characters for alphabet A0.");
                        Console.Error.WriteLine(" -a1 <string>       Define 26 characters for alphabet A1.");
                        Console.Error.WriteLine(" -a2 <string>       Define 23 characters for alphabet A2.");
                        Console.Error.WriteLine("                    Experimental - works best when text encoding is in ISO-8859-1 (C0 or C1).");
                        Console.Error.WriteLine(" -b                 Throw all abbreviations that have lower score than last pick back on heap.");
                        Console.Error.WriteLine("                    (This only occasionally improves the result, use sparingly.)");
                        Console.Error.WriteLine(" -c0                Text character set is plain ASCII only.");
                        Console.Error.WriteLine(" -cu                Text character set is UTF-8.");
                        Console.Error.WriteLine(" -c1                Text character set is ISO 8859-1 (Latin1, ANSI).");
                        Console.Error.WriteLine(" --debug            Prints debug information.");
                        Console.Error.WriteLine(" -i                 The switch is redundant (it will be auto-detected if 'gametext.txt' is in the gamepath).");
                        Console.Error.WriteLine("                    Generate output for Inform6. This requires that the file.");
                        Console.Error.WriteLine("                    'gametext.txt' is in the gamepath. 'gametext.txt' is generated by:");
                        Console.Error.WriteLine("                       inform6 -r $TRANSCRIPT_FORMAT=1 <game>.inf");
                        Console.Error.WriteLine("                    in Inform6 version 6.35 or later. -i always use -r3.");
                        Console.Error.WriteLine(" --infodump <file>  Use text extracted from a compiled file with the ZTool, Infodump.");
                        Console.Error.WriteLine("                    The file is generated by:");
                        Console.Error.WriteLine("                       infodump -io <game> > <game>.infodump");
                        Console.Error.WriteLine("                    (Always used in conjunction with the -txd switch.)");
                        Console.Error.WriteLine(" -n nn              # of abbreviations to generate (default = 96).");
                        Console.Error.WriteLine(" -o 0/input         Output abbreviations in format as the input source (default).");
                        Console.Error.WriteLine("    1/inform        Output abbreviations in Inform6 format.");
                        Console.Error.WriteLine("    2/ZAP           Output abbreviations in ZAP format.");
                        Console.Error.WriteLine(" --onlyrefactor     Skip calculation of abbrevations and only print information about duplicate long strings.");
                        Console.Error.WriteLine(" -r3                Always round to 3 for fast and deep rounding. Normally rounding");
                        Console.Error.WriteLine("                    to 6 is used for strings stored in high memory for z4+ games.");
#if STOPWATCH
                        Console.Error.WriteLine(" --stopwatches      Print detailed timing information on function RescoreOptimalParse. For debugging purposes only.");
#endif
                        Console.Error.WriteLine(" --txd <file>       Use text extracted from a compiled file with the ZTool, Txd.");
                        Console.Error.WriteLine("                    The file is generated by:");
                        Console.Error.WriteLine("                       txd -ag <game> > <game>.txd");
                        Console.Error.WriteLine("                    (Always used in conjunction with the -infodump switch.)");
                        Console.Error.WriteLine(" -v1 - v8           Z-machine version. 1-3: Round to 3 for high strings");
                        Console.Error.WriteLine("                                       4-7: Round to 6 for high strings");
                        Console.Error.WriteLine("                                         8: Round to 12 for high strings");
                        Console.Error.WriteLine(" -v                 Verbose. Prints extra information.");
                        Console.Error.WriteLine(" -x0                Compression level 0, fastest.");
                        Console.Error.WriteLine("                    Pick abbreviations according to highest score with R.A. Wagner's 'Optimal Parse' method.");
                        Console.Error.WriteLine(" -x1                Compression level 1, fast.");
                        Console.Error.WriteLine("                    x0 and adding and removing initial and trailing characters for better z-chars rounding.");
                        Console.Error.WriteLine(" -x2 [n]            Compression level 2, normal. (default)");
                        Console.Error.WriteLine("                    x1 and testing up to n (default n = 10 000) discarded abbreviation variants for better z-chars rounding.");
                        Console.Error.WriteLine(" -x3 [n1] [n2]      Compression level 3, maximum.");
                        Console.Error.WriteLine("                    x2 and testing n2 (default n1 = 10 000, n2 = 1 000) discarded abbreviations as all possible replacements");
                        Console.Error.WriteLine("                    for better z-chars rounding.");
                        Console.Error.WriteLine(" path-to-game       Use this path. If omitted the current path is used.");
                        return;
                    case "-i":
                        inform6StyleText = true;
                        break;
                    case "-c0":
                        TextEncoding = System.Text.Encoding.ASCII;
                        break;
                    case "-cu":
                        TextEncoding = System.Text.Encoding.UTF8;
                        break;
                    case "-c1":
                        TextEncoding = System.Text.Encoding.Latin1;
                        break;
                    case "-v1":
                    case "-v2":
                    case "-v3":
                        zVersion = 3; // Rounding3
                        break;
                    case "-v4":
                    case "-v5":
                    case "-v6":
                    case "-v7":
                        zVersion = 5; // Rounding6
                        break;
                    case "-v8":
                        zVersion = 8; // Rounding12
                        break;
                    case "-x0":
                        compressionLevel = 0;
                        break;
                    case "-x1":
                        compressionLevel = 1;
                        break;
                    case "-x2":
                        compressionLevel = 2;
                        if (i < args.Length - 1 && int.TryParse(args[i + 1], out numberOfPasses)) i += 1; else numberOfPasses = NUMBER_OF_PASSES_DEFAULT;
                        if (numberOfPasses < 1) numberOfPasses= NUMBER_OF_PASSES_DEFAULT;
                        break;
                    case "-x3":
                        compressionLevel = 3;
                        if (i < args.Length - 1 && int.TryParse(args[i + 1], out numberOfPasses)) i += 1; else numberOfPasses = NUMBER_OF_PASSES_DEFAULT;
                        if (i < args.Length - 1 && int.TryParse(args[i + 1], out numberOfDeepPasses)) i += 1; else numberOfDeepPasses = NUMBER_OF_DEEP_PASSES_DEFAULT;
                        if (numberOfPasses < 1) numberOfPasses = NUMBER_OF_PASSES_DEFAULT;
                        if (numberOfPasses < numberOfDeepPasses) numberOfPasses = numberOfDeepPasses;
                        break;
                    case "--infodump":
                        infodumpFilename = args[i + 1];
                        i += 1;
                        break;
                    case "--txd":
                        txdFilename = args[i + 1];
                        i += 1;
                        break;
                    case "-o":
                        if (args.Length > i + 1)
                        {
                            if (args[i + 1] == "0" || args[i + 1].Equals("input", StringComparison.CurrentCultureIgnoreCase))
                            {
                                outputFormat = 0;
                                i += 1;
                            }
                            else if (args[i + 1] == "1" || args[i + 1].Equals("inform", StringComparison.CurrentCultureIgnoreCase))
                            {
                                outputFormat = 1;
                                i += 1;
                            }
                            else if (args[i + 1] == "2" || args[i + 1].Equals("ZAP", StringComparison.CurrentCultureIgnoreCase))
                            {
                                outputFormat = 2;
                                i += 1;
                            }
                        }
                        break;
                    case "--onlyrefactor":
                        onlyRefactor = true;
                        break;
#if STOPWATCH
                    case "--stopwatches":
                        stopwatches = true;
                        break;
#endif
                    default:
                        if (System.IO.Directory.Exists(args[i]))
                        {
                            gameDirectory = args[i];
                        }
                        break;
                }
            }

            // Console.SetCursorPosition and Console.GetCursorPosition don't work if output is redirected
            if (Console.IsOutputRedirected || Console.IsErrorRedirected) OutputRedirected = true;
            if (forceRoundingTo3) zVersion = 3;
            if (zVersion == 0)
            {
                zVersion = 3; // Default to Rounding3
                tryAutoDetectZVersion = true;
            }

            // Auto-detect Inform
            if (!inform6StyleText & System.IO.File.Exists(System.IO.Path.Combine(gameDirectory, "gametext.txt")))
                inform6StyleText = true;

            SearchForAbbreviations(gameDirectory, inform6StyleText, throwBackLowscorers, printDebug);
        }

        //Algorithm, suggested by MTR
        //1.  Calculate abbreviations, score by naive savings
        //2.  Put them in a max-heap.
        //3.  Remove top of heap abbreviation, add To the set of best abbreviations And parse entire corpus.
        //4.  Compute change In savings (Using optimal parse) And declare that to be the new score for the current abbreviation.
        //5.  If the new score is less than the current score for the top-of-heap, remove the current abbreviation from the 
        //    best_abbreviations set And throw it back on the heap.
        //6.  Repeat from step 3 until enough abbreviations are found or the heap is empty.

        // See:
        // https://intfiction.org/t/highly-optimized-abbreviations-computed-efficiently/48753
        // https://intfiction.org/t/playable-version-of-mini-zork-ii/49326
        // https://gitlab.com/russotto/zilabbrs
        // https://github.com/hlabrand/retro-scripts

        private static void SearchForAbbreviations(string gameDirectory, bool inform6StyleText, bool throwBackLowscorers, bool printDebug)
        {
            try
            {

                //**********************************************************************************************************************
                //***** Step 1: Reading file(s) and storing all strings in a collection                                            *****
                //**********************************************************************************************************************

#if STOPWATCH
                sw1.Reset();
                sw2.Reset();
                sw3.Reset();
                sw4.Reset();
                sw5.Reset();
                callCount = 0;
#endif
                // Set CultureInfo for this thread
                CultureInfo ci = CultureInfo.CreateSpecificCulture("");  // InvariantCulture
                ci.NumberFormat.NumberGroupSeparator = " ";
                Thread.CurrentThread.CurrentCulture = ci;
                Thread.CurrentThread.CurrentUICulture = ci;

                // Define and start stopwatches to measure times and a objekt to read memory consumption
                Stopwatch swTotal = Stopwatch.StartNew();
                Stopwatch swPart = Stopwatch.StartNew();
                Process proc = Process.GetCurrentProcess();

                Console.Error.WriteLine("ZAbbrev 0.11 ({0}) by Henrik Åsman, (c) 2021-2024", buildTimestamp);
                Console.Error.WriteLine("Highly optimized abbreviations computed efficiently");

                // Read file(s) inte one large text string and replace space, quote and LF.
                // Also count frequency of characters for potential custom alphabet
                bool searchFor34 = false;
                bool searchForCR = false;
                List<GameText> gameTextList = [];
                int totalSavings = 0;
                string gameFilename = "";
                bool packedAddress = false;
                Dictionary<char, int> charFreq = [];
                int totalCharacters = 0;
                int routineID = 0;

                Console.Error.WriteLine();
                Console.Error.WriteLine("Processing files in directory: {0}", gameDirectory);
                if (compressionLevel == 0) Console.Error.WriteLine("Compression level            : fastest");
                if (compressionLevel == 1) Console.Error.WriteLine("Compression level            : fast");
                if (compressionLevel == 2)
                {
                    Console.Error.WriteLine("Compression level            : normal (n = {0:##,#})", numberOfPasses);
                }
                if (compressionLevel == 3)
                {
                    Console.Error.WriteLine("Compression level            : maximum (n1 = {0:##,#}, n2 = {1:##,#})", numberOfPasses,numberOfDeepPasses);
                }
                Console.Error.WriteLine();
                Console.Error.WriteLine("Progress                               Time (s) Mem (MB)");
                Console.Error.WriteLine("--------                               -------- --------");
                Console.Error.Write("Reading file...".PadRight(40));
                if (!System.IO.Directory.Exists(gameDirectory))
                {
                    Console.Error.WriteLine("ERROR: Can't find specified directory.");
                    return;
                }
                bool useTxd = false;
                if (infodumpFilename != "" || txdFilename != "") useTxd = true;

                if (infodumpFilename != "" && !System.IO.File.Exists(System.IO.Path.Combine(gameDirectory, infodumpFilename)))
                {
                    Console.Error.WriteLine("ERROR: Can't find infodump-file.");
                    return;
                }
                if (txdFilename != "" && !System.IO.File.Exists(System.IO.Path.Combine(gameDirectory, txdFilename)))
                {
                    Console.Error.WriteLine("ERROR: Can't find txd-file.");
                    return;
                }

                if (inform6StyleText && !useTxd)
                {
                    // Inform6 text are in "gametext.txt". 
                    // "gametext.txt" is produced by: inform6.exe -r $TRANSCRIPT_FORMAT=1 <gamefile>.inf
                    // Each line is coded
                    //   I:info                          not in game file, don't index
                    //   G:game text                     high strings, index and packed address
                    //   V:veneer text                   high strings, index and packed address
                    //   L:lowmem string                 stored in abbreviation area, index?
                    //   A:abbreviation                  don't index
                    //   D:dict word                     don't index
                    //   O:object name                   obj desc, index
                    //       The metaclasses objects Class, Object, Routine and String are
                    //       created before abbreviations are defined and don't use them.
                    //       Therefore they should not be part of index.
                    //   S:symbol                        high strings, index and packed address
                    //   X:infix                         debug text, don't index
                    //   H:game text inline in opcode    text stored inline with opcode, index
                    //   W:veneer text inline in opcode  text stored inline with opcode, index
                    // ^ means CR and ~ means ".
                    // Candidate strings that contains a @ should not be considered.
                    // 6.42+ will add "I: Compiled Z-machine version 5" to gametext.txt
                    if (System.IO.File.Exists(System.IO.Path.Combine(gameDirectory, "gametext.txt")))
                    {
                        if (TextEncoding is null)
                        {
                            //Try to autodetect encoding
                            if (IsFileUTF8(System.IO.Path.Combine(gameDirectory, "gametext.txt")))
                                TextEncoding = System.Text.Encoding.UTF8;
                            else
                                TextEncoding = System.Text.Encoding.Latin1;
                        }

                        System.IO.StreamReader reader = new(System.IO.Path.Combine(gameDirectory, "gametext.txt"), TextEncoding);
                        string line = null;
                        int objectNumber = 0;
                        do
                        {
                            line = reader.ReadLine();
                            if (line is not null)
                            {
                                if ("GVLOSHW".Contains(line[0]))
                                {
                                    // Replace ^, ~ and space
                                    line = line.Replace("^", LF_REPLACEMENT.ToString());
                                    line = line.Replace("~", QUOTE_REPLACEMENT.ToString());
                                    line = line.Replace(" ", SPACE_REPLACEMENT.ToString());

                                    if ("GVS".Contains(line[0]))
                                        packedAddress = true;
                                    else
                                        packedAddress = false;

                                    GameText gameTextLine = new(line[3..]) { packedAddress = packedAddress };
                                    if (line[0] == 'O')
                                    {
                                        gameTextLine.objectDescription = true;
                                        objectNumber += 1;
                                    }
                                    if (line[0] == 'H')
                                        gameTextLine.routineID = routineID;
                                    if (!(objectNumber < 6 && (line == "O:^Class" || line == "O:^Object" || line == "O:^Routine" || line == "O:^String")))
                                        gameTextList.Add(gameTextLine);
                                    totalCharacters += gameTextLine.TextAsSpan.Length;

                                    // Add characters to charFreq
                                    for (int i = 3; i < line.Length; i++)
                                    {
                                        char c = line[i];
                                        if (!(c == LF_REPLACEMENT || c == QUOTE_REPLACEMENT || c == SPACE_REPLACEMENT || ASCII(c) == 27))
                                        {
                                            charFreq.TryAdd(c, 0);
                                            charFreq[c] += 1;
                                        }
                                    }
                                }
                                else
                                {
                                    if (line.StartsWith("I: [Compiled Z-machine version") && tryAutoDetectZVersion)
                                        zVersion = int.Parse(line[31].ToString());
                                    if (line.Contains("without inline strings size:"))
                                    {
                                        int iStart = line.IndexOf("without inline strings size:") + 29;
                                        int iLength = line.IndexOf(' ', iStart) - iStart;
                                        routineSize.Add(int.Parse(line.Substring(iStart, iLength)));
                                        routineID += 1;
                                    }
                                }
                            }
                        } while (line is not null);
                        reader.Close();
                    }
                    else
                    {
                        Console.Error.WriteLine();
                        Console.Error.WriteLine("ERROR: Found no 'gametext.txt' in directory.");
                        return;
                    }
                }

                if (!inform6StyleText && !useTxd)
                {
                    // Get text from zap-files and store every line in a list of strings.
                    // The ".GSTR", ".STRL", "PRINTI" and "PRINTR" Op-codes contains the text.
                    // Every pattern is stored in a dictionary with the pattern as key.
                    foreach (string fileName in System.IO.Directory.GetFiles(gameDirectory))
                    {
                        int startPos = 0;

                        if (string.Equals(System.IO.Path.GetExtension(fileName), ".ZAP", StringComparison.OrdinalIgnoreCase) && !fileName.Contains("_freq", StringComparison.OrdinalIgnoreCase))
                        {
                            if (gameFilename == "" || System.IO.Path.GetFileName(fileName).Length < gameFilename.Length)
                                gameFilename = System.IO.Path.GetFileName(fileName);

                            if (TextEncoding is null)
                            {
                                if (IsFileUTF8(fileName))
                                    TextEncoding = System.Text.Encoding.UTF8;
                                else
                                    TextEncoding = System.Text.Encoding.Latin1;
                            }

                            byte[] byteText = System.IO.File.ReadAllBytes(fileName);

                            int textLength = byteText.Length;
                            for (int i = 5; i < textLength; i++)
                            {
                                string opCodeString = TextEncoding.GetString(byteText, i - 5, 5).ToUpper();
                                bool objectDescription = false;
                                if (opCodeString == ".GSTR") // High strings
                                {
                                    searchFor34 = true;
                                    packedAddress = true;
                                }
                                if (opCodeString == ".STRL") // Object descriptions
                                {
                                    searchFor34 = true;
                                    packedAddress = false;
                                    objectDescription = true;
                                }
                                if (opCodeString == "RINTI") // Prints text inline
                                {
                                    searchFor34 = true;
                                    packedAddress = false;
                                }
                                if (opCodeString == "RINTR") // Prints text inline + CRLF + RTRUE
                                {
                                    searchFor34 = true;
                                    packedAddress = false;
                                }
                                // zversion is only relevant if we want to round to 6 zchars for strings in high memory
                                // ZAPF inserts the file in this order:
                                //   game_freq.zap
                                //   game_data.zap
                                //   game.zap
                                //   game_str.zap
                                //
                                //   dynamic memory : Everything to the label IMPURE (game_data.zap)
                                //   static memory  : Between IMPURE and ENDLOD (game_data.zap)
                                //   high memory    : Everything after ENDLOD
                                //
                                //   Only .GSTR is relevant for rounding to anything other than 3 because text
                                //   in game.zap (inside code) always rounds to 3.
                                if (opCodeString == ".NEW " && tryAutoDetectZVersion)
                                {
                                    zVersion = byteText[i] - 48;
                                    if (zVersion < 4) //Rounding3
                                        zVersion = 3;
                                    if (zVersion > 3 && zVersion < 8) //Rounding6, version 8 --> rounding12
                                        zVersion = 5;
                                }

                                if (searchFor34 && byteText[i] == 34)
                                {
                                    startPos = i;
                                    searchFor34 = false;
                                    searchForCR = true;
                                }

                                if (searchForCR && byteText[i] == 13)
                                {
                                    searchForCR = false;

                                    // Replace ", [LF] & Space with printable and legal characters for a Key
                                    if ((i - startPos - 2) > 0)
                                    {
                                        byte[] byteTemp = new byte[i - startPos - 2];
                                        for (int j = 0; j < byteTemp.Length; j++)
                                        {
                                            byte byteChar = byteText[startPos + 1 + j];
                                            if (byteChar == 10) byteChar = ASCII(LF_REPLACEMENT);
                                            if (byteChar == 32) byteChar = ASCII(SPACE_REPLACEMENT);
                                            if (byteChar == 34) byteChar = ASCII(QUOTE_REPLACEMENT);
                                            byteTemp[j] = byteChar;
                                        }

                                        // Create dictionary. Replace two double-quotes with one (the first is an escape-char). 
                                        GameText gameTextLine = new(TextEncoding.GetString(byteTemp).Replace(string.Concat(QUOTE_REPLACEMENT, QUOTE_REPLACEMENT), QUOTE_REPLACEMENT.ToString()))
                                        {
                                            packedAddress = packedAddress,
                                            objectDescription = objectDescription
                                        };
                                        gameTextList.Add(gameTextLine);
                                        totalCharacters += gameTextLine.TextAsSpan.Length;

                                        // Add characters to charFreq
                                        for (int j = 0; j < gameTextLine.text.Length; j++)
                                        {
                                            char c = gameTextLine.text[j];
                                            if (!(c == LF_REPLACEMENT || c == QUOTE_REPLACEMENT || c == SPACE_REPLACEMENT || ASCII(c) == 27))
                                            {
                                                charFreq.TryAdd(c, 0);
                                                charFreq[c] += 1;
                                            }
                                        }

                                    }
                                }
                            }
                        }
                    }
                }

                if (useTxd)
                {
                    // Get text from output generated by the ZTools, Infodump and TXD.
                    // infodump needs the switch -o and -i:
                    //       infodump -io <gamefile> > <gamefile>.infodump
                    // txd need the switch -a to format text in Inform style
                    //       txd -ag <gamefile> > <gamefile>.txd
                    // Inform/ZIL and version are determined by header info. If header-info is missing ZIL, version 3 is assumed.
                    if (IsFileUTF8(System.IO.Path.Combine(gameDirectory, infodumpFilename)))
                        TextEncoding = System.Text.Encoding.UTF8;
                    else
                        TextEncoding = System.Text.Encoding.Latin1;

                    byte[] byteInfodump = System.IO.File.ReadAllBytes(System.IO.Path.Combine(gameDirectory, infodumpFilename));
                    int startPos = 0;
                    searchFor34 = false;
                    int textLength = byteInfodump.Length;
                    for (int i = 13; i < textLength; i++)
                    {
                        string infodumpString = TextEncoding.GetString(byteInfodump, i - 13, 13).ToUpper();
                        if (infodumpString == "DESCRIPTION: ") searchFor34 = true;
                        if (infodumpString == "Z-CODE VERSIO") zVersion = byteInfodump[i + 13] - 48;
                        if (infodumpString == "INFORM VERSIO")
                        {
                            string sTemp = TextEncoding.GetString(byteInfodump, i + 5, 13).ToUpper().Trim();
                            if (sTemp != "ZAPF") inform6StyleText = true;
                        }

                        if (searchFor34 && byteInfodump[i] == 34)
                        {
                            startPos = i;
                            searchFor34 = false;
                            searchForCR = true;
                        }

                        if (searchForCR && byteInfodump[i] == 13)
                        {
                            searchForCR = false;

                            // Replace ", [LF] & Space with printable and legal characters for a Key
                            if ((i - startPos - 2) > 0)
                            {
                                byte[] byteTemp = new byte[i - startPos - 2];
                                for (int j = 0; j < byteTemp.Length; j++)
                                {
                                    byte byteChar = byteInfodump[startPos + 1 + j];
                                    if (byteChar == 10 || byteChar == 94) byteChar = ASCII(LF_REPLACEMENT);
                                    if (byteChar == 32) byteChar = ASCII(SPACE_REPLACEMENT);
                                    if (byteChar == 34) byteChar = ASCII(QUOTE_REPLACEMENT);
                                    byteTemp[j] = byteChar;
                                }

                                // Create dictionary. Replace two double-quotes with one (the first is an escape-char). 
                                GameText gameTextLine = new(TextEncoding.GetString(byteTemp).Replace(string.Concat(QUOTE_REPLACEMENT, QUOTE_REPLACEMENT), QUOTE_REPLACEMENT.ToString()))
                                {
                                    packedAddress = false,
                                    objectDescription = true
                                };
                                gameTextList.Add(gameTextLine);
                                totalCharacters += gameTextLine.TextAsSpan.Length;

                                // Add characters to charFreq
                                for (int j = 0; j < gameTextLine.text.Length; j++)
                                {
                                    char c = gameTextLine.text[j];
                                    if (!(c == LF_REPLACEMENT || c == QUOTE_REPLACEMENT || c == SPACE_REPLACEMENT || ASCII(c) == 27))
                                    {
                                        charFreq.TryAdd(c, 0);
                                        charFreq[c] += 1;
                                    }
                                }

                            }
                        }
                    }

                    if (IsFileUTF8(System.IO.Path.Combine(gameDirectory, txdFilename)))
                        TextEncoding = System.Text.Encoding.UTF8;
                    else
                        TextEncoding = System.Text.Encoding.Latin1;

                    byte[] byteTxd = System.IO.File.ReadAllBytes(System.IO.Path.Combine(gameDirectory, txdFilename));
                    startPos = 0;
                    searchFor34 = false;
                    bool codeArea = true;
                    packedAddress = false;
                    int texgtLength = byteTxd.Length;
                    for (int i = 9; i < texgtLength; i++)
                    {
                        string txdString = TextEncoding.GetString(byteTxd, i - 9, 9).ToUpper();
                        if (codeArea && txdString == "PRINT    ") searchFor34 = true;
                        if (codeArea && txdString == "PRINT_RET") searchFor34 = true;
                        if (txdString == "D OF CODE")
                        {
                            codeArea = false;
                            searchFor34 = true;
                            packedAddress = true;
                        }
                        if (searchFor34 && byteTxd[i] == 34)
                        {
                            startPos = i;
                            searchFor34 = false;
                            searchForCR = true;
                            i += 1;
                        }
                        if (searchForCR && byteTxd[i] == 34)
                        {
                            searchForCR = false;
                            if (!codeArea) searchFor34 = true;

                            // Replace ", [LF] & Space with printable and legal characters for a Key
                            if ((i - startPos - 1) > 0)
                            {
                                byte[] byteTemp = new byte[i - startPos - 1];
                                for (int j = 0; j < byteTemp.Length; j++)
                                {
                                    byte byteChar = byteTxd[startPos + 1 + j];
                                    if (byteChar == 13) byteChar = ASCII('}'); // Supress CR
                                    if (byteChar == 10) byteChar = 32;         // Convert LF to SPACE
                                    if (byteChar == 94) byteChar = ASCII(LF_REPLACEMENT);
                                    if (byteChar == 32) byteChar = ASCII(SPACE_REPLACEMENT);
                                    if (byteChar == 34) byteChar = ASCII(QUOTE_REPLACEMENT);
                                    byteTemp[j] = byteChar;
                                }

                                // Create dictionary. Replace two double-quotes with one (the first is an escape-char). 
                                GameText gameTextLine = new(TextEncoding.GetString(byteTemp).Replace(string.Concat(QUOTE_REPLACEMENT, QUOTE_REPLACEMENT), QUOTE_REPLACEMENT.ToString()).Replace("}", "")) { packedAddress = packedAddress };
                                gameTextList.Add(gameTextLine);
                                totalCharacters += gameTextLine.TextAsSpan.Length;

                                // Add characters to charFreq
                                for (int j = 0; j < gameTextLine.text.Length; j++)
                                {
                                    char c = gameTextLine.text[j];
                                    if (!(c == LF_REPLACEMENT || c == QUOTE_REPLACEMENT || c == SPACE_REPLACEMENT || ASCII(c) == 27))
                                    {
                                        charFreq.TryAdd(c, 0);
                                        charFreq[c] += 1;
                                    }
                                }

                            }
                        }
                    }

                }

                // Adjust outputformat if input is overridden
                if (outputFormat == 1) inform6StyleText = true;
                if (outputFormat == 2) inform6StyleText = false;

                proc.Refresh();
                swPart.Stop();
                Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} characters, {3}", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), totalCharacters, string.Concat(TextEncoding.BodyName, ", ", TextEncoding.EncodingName));

                //**********************************************************************************************************************
                //***** Step 2: Fix alphabet and build a suffix array over all strings                                             *****
                //**********************************************************************************************************************

                swPart = Stopwatch.StartNew();
                Console.Error.Write("Building suffix arrays...".PadRight(40));

                if (customAlphabet)
                {
                    List<KeyValuePair<char, int>> charFreqList = [.. (
                        from KeyValuePair<char, int> tPair in charFreq
                        orderby tPair.Value descending
                        select tPair)];

                    // Caclculate cost with default alphabet
                    foreach (char c in alphabet0) alphabet0Hash.Add(c);
                    alphabet0Hash.Add(SPACE_REPLACEMENT);

                    foreach (char c in alphabet1) alphabet1And2Hash.Add(c);
                    foreach (char c in alphabet2) alphabet1And2Hash.Add(c);
                    alphabet1And2Hash.Add(QUOTE_REPLACEMENT);
                    alphabet1And2Hash.Add(LF_REPLACEMENT);

                    foreach (GameText gameTextLine in gameTextList) gameTextLine.costWithDefaultAlphabet = ZstringCost(gameTextLine.text);
                    alphabet0Hash.Clear();
                    alphabet1And2Hash.Clear();

                    string alphabet = "";
                    for (int i = 0; i <= 74; i++) alphabet = string.Concat(alphabet, charFreqList[i].Key);
                    alphabet0 = SortAlphabet(alphabet[..26], defaultA0);
                    alphabet1 = SortAlphabet(alphabet.Substring(26, 49), string.Concat(defaultA1, defaultA2));
                    alphabet2 = alphabet1[26..];
                    alphabet1 = alphabet1[..26];
                    if (printDebug)
                    {
                        Console.Error.WriteLine();
                        Console.Error.WriteLine();
                        Console.Error.WriteLine(string.Concat("Alphabet = ", (char)34, alphabet, (char)34));
                        Console.Error.WriteLine();
                        Console.Error.Write(new string(' ', 40));
                    }
                }

                // Store alphabet in hashsets (slightly faster) and add SPACE_REPLACEMENT to A0 and
                // other replacements to A2 because zcharcost becomes more optimized without OrElse
                foreach (char c in alphabet0) alphabet0Hash.Add(c);
                alphabet0Hash.Add(SPACE_REPLACEMENT);
                foreach (char c in alphabet1) alphabet1And2Hash.Add(c);
                foreach (char c in alphabet2) alphabet1And2Hash.Add(c);
                alphabet1And2Hash.Add(QUOTE_REPLACEMENT);
                alphabet1And2Hash.Add(LF_REPLACEMENT);
                if (customAlphabet)
                    foreach (GameText gameTextLine in gameTextList) gameTextLine.costWithCustomAlphabet = ZstringCost(gameTextLine.text);

                //Build a suffix array
                List<string> texts = [];
                Dictionary<string, PatternData> patternDictionary = []; // Use a dictionary to filter out duplicates of patterns
                for (int i = 0; i < gameTextList.Count; i++)
                {
                    texts.Add(gameTextList[i].text);
                    gameTextList[i].suffixArray = SuffixArray.BuildSuffixArray(gameTextList[i].text);
                    gameTextList[i].lcpArray = SuffixArray.BuildLCPArray(gameTextList[i].text, gameTextList[i].suffixArray);
                }
                string gsaString = SuffixArray.BuildGeneralizedSuffixArrayString(texts);
                int[] sa = SuffixArray.BuildSuffixArray(gsaString);
                int[] lcp = SuffixArray.BuildLCPArray(gsaString, sa);
                proc.Refresh();
                swPart.Stop();
                Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} potential patterns", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), SuffixArray.CountUniquePatterns(lcp));

                //**********************************************************************************************************************
                //***** Step 3: Extract all unique patterns from strings using suffix array and store in a dictionary              *****
                //*****         Calculates cost and frequency of all patterns.                                                     *****
                //**********************************************************************************************************************

                swPart = Stopwatch.StartNew();
                Console.Error.Write("Extracting viable patterns...".PadRight(40));
                int lcpLength = lcp.Length - 2;
                for (int i = SuffixArray.Count(lcp, 0, 1); i <= lcpLength; i++) // The iteration kan skip all suffixes that start with the seperator
                {
                    if (lcp[i + 1] > 0) // patterns with lcp=0 have a frequency of 1 and can be discarded
                    {
                        int start = 1;
                        if (i > 0)
                        {
                            start = lcp[i];
                        }
                        if (start < 1)
                        {
                            start = 1;
                        }
                        int lcpTemp = lcp[i + 1];
                        for (int j = start; j <= lcpTemp; j++)
                        {
                            string sKey = gsaString.Substring(sa[i], j);
                            if (!sKey.Contains('\v') && !sKey.Contains('@'))
                            {
                                int cost = ZstringCost(sKey);
                                int freq = SuffixArray.Count(lcp, i, sKey.Length);
                                if (freq > 1 && (freq * (cost - 2)) - ((cost + 2) / 3) * 3 > 0) // Same formula as in PatternData.Score
                                {
                                    if (!patternDictionary.ContainsKey(sKey))
                                    {
                                        // New potential pattern, add it to dictionary
                                        patternDictionary[sKey] = new PatternData
                                        {
                                            Cost = cost,
                                            Frequency = freq,
                                            Key = sKey
                                        };
                                    }
                                }
                            }
                        }
                    }
                }
                if (gameTextList.Count == 0)
                {
                    Console.Error.WriteLine("ERROR: No data to index.");
                    return;
                }
                swPart.Stop();
                proc.Refresh();
                Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} strings, {3:##,#} patterns extracted", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), gameTextList.Count, patternDictionary.Count);

                //**********************************************************************************************************************
                //***** Step 4: Put all patterns up to 20 characters on a max heap. For patterns longer than 20 characters only    *****
                //*****         the patterns that don't contains a subpattern. The max heap have the one with highest potential    *****
                //*****         savings are on top.                                                                                *****
                //**********************************************************************************************************************

                // Add to a Max Heap
                swPart = Stopwatch.StartNew();
                Console.Error.Write("Build max heap with naive score...".PadRight(40));
                PriorityQueue<PatternData, int> maxHeap = new(new PatternComparer());
                PriorityQueue<PatternData, int> maxHeapRefactor = new(new PatternComparer());
                PriorityQueue<PatternData, int> maxHeapLength = new(new PatternComparer());
                foreach (KeyValuePair<string, PatternData> phraseRevisedIterator in patternDictionary)
                {
                    KeyValuePair<string, PatternData> phrase = phraseRevisedIterator;
                    phrase.Value.Savings = phrase.Value.Score;
                    if (phrase.Value.Savings > 0)
                    {
                        if (phrase.Key.Length <= CUTOFF_LONG_PATTERN)
                        {
                            // Save all short patterns
                            maxHeap.Enqueue(phrase.Value, phrase.Value.Savings);
                        }
                        else
                        {
                            // Store longer patterns for later  
                            maxHeapLength.Enqueue(phrase.Value, phrase.Key.Length);
                        }
                    }
                }
                // Only save the longest pattern and not the substrings that are contained inside them
                HashSet<string> tempHashSet = [];
                while (maxHeapLength.Count > 0)
                {
                    PatternData candidate = maxHeapLength.Dequeue();
                    tempHashSet.Add(candidate.Key[1..]);
                    tempHashSet.Add(candidate.Key[..^1]);
                    if (!tempHashSet.Contains(candidate.Key))
                    {
                        maxHeap.Enqueue(candidate, candidate.Savings);
                        maxHeapRefactor.Enqueue(candidate, candidate.Key.Length);
                    }
                }
                tempHashSet = null;
                maxHeapLength = null;
                swPart.Stop();
                proc.Refresh();
                Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} patterns added to heap", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), maxHeap.Count);

                //**********************************************************************************************************************
                //***** Step 5: Pick abbreviations from heap and rescore them with Wagner's method for optimal parse. (Fastest)    *****
                //**********************************************************************************************************************

                // Optimal Parse
                List<PatternData> bestCandidateList = [];
                int currentAbbrev = 0;
                int previousSavings = 0;
                int oversample = 0;
                int latestTotalBytes = 0;

                // Init the total rounding penalty without abbreviations
                totalSavings = 0;
                if (throwBackLowscorers) oversample = 5;
                if (!onlyRefactor)
                {
                    swPart = Stopwatch.StartNew();
                    Console.Error.Write("Rescoring with optimal parse...".PadRight(40));
                    if (printDebug) Console.Error.WriteLine();
                    if (!OutputRedirected && !printDebug)
                    {
                        Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                        Console.Write("{0,3}%", 0);
                    }
                    if (printDebug) Console.Error.WriteLine();

                    do
                    {
                        PatternData candidate = maxHeap.Dequeue();
                        bestCandidateList.Add(candidate);
                        int currentSavings = RescoreOptimalParse(gameTextList, bestCandidateList, false, zVersion);
                        int deltaSavings = currentSavings - previousSavings;
                        if (deltaSavings < maxHeap.Peek().Savings)
                        {
                            // If delta savings is less than top of heap then remove current abbrev and reinsert it in heap with new score and try next from heap
                            PatternData KPD = bestCandidateList[currentAbbrev];
                            KPD.Savings = deltaSavings;
                            bestCandidateList.RemoveAt(currentAbbrev);
                            maxHeap.Enqueue(KPD, KPD.Savings);
                        }
                        else
                        {
                            if (printDebug)
                                Console.Error.WriteLine("Adding abbrev no " + (currentAbbrev + 1).ToString() + ": " + FormatAbbreviation(bestCandidateList[currentAbbrev].Key) + ", Total savings: " + currentSavings.ToString());
                            int latestSavings = currentSavings - previousSavings;
                            currentAbbrev += 1;
                            previousSavings = currentSavings;
                            totalSavings = currentSavings;
                            if (throwBackLowscorers)
                            {
                                // put everthing back on heap that has lower savings than latest added
                                bool bNeedRecalculation = false;
                                for (int i = bestCandidateList.Count - 1; i >= 0; i--)
                                {
                                    if (bestCandidateList[i].Savings < latestSavings)
                                    {
                                        if (printDebug)
                                            Console.Error.WriteLine("Removing abbrev: " + FormatAbbreviation(bestCandidateList[i].Key));
                                        maxHeap.Enqueue(bestCandidateList[i], bestCandidateList[i].Savings);
                                        bestCandidateList.RemoveAt(i);
                                        i -= 1;
                                        currentAbbrev -= 1;
                                        bNeedRecalculation = true;
                                    }
                                }
                                if (bNeedRecalculation)
                                {
                                    previousSavings = RescoreOptimalParse(gameTextList, bestCandidateList, false, zVersion);
                                    if (printDebug)
                                        Console.Error.WriteLine("Total savings: " + previousSavings.ToString() + " - Total Abbrevs: " + currentAbbrev.ToString());
                                }
                            }
                        }

                        int progress = Convert.ToInt32(currentAbbrev * 100 / (double)(NumberOfAbbrevs + oversample));
                        if (!OutputRedirected && !printDebug && progress % 5 == 0)
                        {
                            Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                            Console.Write("{0,3}%", progress);
                        }

                    } while (!(currentAbbrev == (NumberOfAbbrevs + oversample) || maxHeap.Count == 0));
                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                    if (printDebug)
                    {
                        Console.Error.WriteLine();
                        Console.Error.Write(new string(' ', 40));
                    }
                    swPart.Stop();
                    proc.Refresh();
                    if (!OutputRedirected && !printDebug)
                    {
                        Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                        Console.Write("{0,3}% ", 100);
                    }
                    Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  Total saving {2:##,#} z-chars, text size = {3:##,#} bytes", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), totalSavings, latestTotalBytes);

                    if (printDebug)
                    {
                        Console.Error.WriteLine();
                        if (inform6StyleText)
                            PrintAbbreviationsI6(AbbrevSort(bestCandidateList, false), true);
                        else
                            PrintAbbreviations(AbbrevSort(bestCandidateList, false), gameFilename, true);
                        Console.Error.WriteLine();
                    }

                    // Restore best candidate list to numberOfAbbrevs patterns
                    for (int i = (NumberOfAbbrevs + oversample - 1); i >= NumberOfAbbrevs; i--)
                    {
                        maxHeap.Enqueue(bestCandidateList[i], bestCandidateList[i].Savings);
                        bestCandidateList.RemoveAt(i);
                    }
                }

                //**********************************************************************************************************************
                //***** Step 6: x2-3. Try potential abbreviations to see if they save bytes by minimizing the space lost           *****
                //*****         to padding.                                                                                        *****
                //**********************************************************************************************************************

                int previousTotalBytes = 0;
                if (!onlyRefactor)
                {
                    totalSavings = 0;
                    if (compressionLevel > 1)
                    {
                        // Ok, we now have numberOfAbbrevs abbreviations
                        // Recalculate savings taking rounding into account and test a number of candidates to see if they yield a better result.
                        // This can't be done exactly because strings that are inline the z-code on z4+ have the rounding cost for packed addresses
                        // shared between potentially multiple string inside the same code block and the code-block itself. Sometimes the saving
                        // can be better if ignoring rounding > 3 and force it to 3 with (-r3).
                        swPart = Stopwatch.StartNew();
                        Console.Error.Write("Refining picked abbreviations... ".PadRight(40));
                        if (printDebug) Console.Error.WriteLine();
                        if (!OutputRedirected && !printDebug)
                        {
                            Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                            Console.Write("{0,3}%", 0);
                        }
                        if (printDebug) Console.Error.WriteLine();
                        int passes = 0;
                        previousTotalBytes = latestTotalBytes;
                        int maxAbbreviationLength = 0;
                        for (int i = 0; i < bestCandidateList.Count; i++)
                        {
                            if (bestCandidateList[i].Key.Length > maxAbbreviationLength && bestCandidateList[i].Key.Length <= CUTOFF_LONG_PATTERN)
                                maxAbbreviationLength = bestCandidateList[i].Key.Length;
                        }
                        maxAbbreviationLength += 2;

                        // Add refining abbreviations for -x2, -x3
                        while (passes < numberOfPasses && maxHeap.Count > 0)
                        {
                            PatternData runnerup = maxHeap.Dequeue();
                            if (runnerup.Key.Length > maxAbbreviationLength)
                                continue;
                            passes += 1;
                            if (!OutputRedirected && passes % (numberOfPasses / 20.0) == 0)
                            {
                                if (printDebug)
                                    Console.WriteLine("{0,3}%", Convert.ToInt32(passes / (numberOfPasses / 100.0)));
                                else
                                {
                                    Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                                    Console.Write("{0,3}%", Convert.ToInt32(passes / (numberOfPasses / 100.0)));
                                }
                            }

                            if (compressionLevel > 2 && passes < numberOfDeepPasses)
                            {

                                //    ' Maximum
                                if (!OutputRedirected && passes % (numberOfPasses / 100.0) == 0)
                                {
                                    if (printDebug)
                                        Console.WriteLine("{0,3}%", Convert.ToInt32(passes / (numberOfPasses / 100.0)));
                                    else
                                    {
                                        Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                                        Console.Write("{0,3}%", Convert.ToInt32(passes / (numberOfPasses / 100.0)));
                                    }
                                }
                                int bestDelta = 0;
                                int bestIndex = -1;
                                int bestTotalBytes = 0;
                                int listCount = bestCandidateList.Count;
                                for (var i = 0; i < listCount; i++) // To 0 Step -1
                                {
                                    PatternData tempCandidate = bestCandidateList[i];
                                    bestCandidateList[i] = runnerup;
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > bestDelta)
                                    {
                                        bestDelta = deltaSavings;
                                        bestIndex = i;
                                        bestTotalBytes = latestTotalBytes;
                                    }
                                    bestCandidateList[i] = tempCandidate;
                                }
                                if (bestIndex != -1)
                                {
                                    previousTotalBytes = bestTotalBytes;
                                    if (printDebug)
                                        Console.Error.WriteLine("Replacing " + FormatAbbreviation(bestCandidateList[bestIndex].Key) + " with " + FormatAbbreviation(runnerup.Key) + ", saving " + bestDelta.ToString() + " bytes, pass = " + passes.ToString());
                                    bestCandidateList[bestIndex] = runnerup;
                                }

                            }
                            else
                            {

                                // Normal
                                int listCount = bestCandidateList.Count;
                                for (var i = 0; i < listCount; i++)
                                {
                                    if (runnerup.Key.Contains(bestCandidateList[i].Key) || bestCandidateList[i].Key.Contains(runnerup.Key))
                                    {
                                        PatternData tempCandidate = bestCandidateList[i];
                                        bestCandidateList[i] = runnerup;
                                        latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                        int deltaSavings = previousTotalBytes - latestTotalBytes;
                                        if (deltaSavings > 0)
                                        {
                                            previousTotalBytes = latestTotalBytes;
                                            if (printDebug)
                                                Console.Error.WriteLine("Replacing " + FormatAbbreviation(tempCandidate.Key) + " with " + FormatAbbreviation(runnerup.Key) + ", saving " + deltaSavings.ToString() + " bytes, pass = " + passes.ToString());
                                            break; // Replaced, no need to check for more
                                        }
                                        else
                                            bestCandidateList[i] = tempCandidate;
                                    }
                                }

                            }
                        }

                        latestTotalBytes = previousTotalBytes;
                        totalSavings = RescoreOptimalParse(gameTextList, bestCandidateList, false, zVersion);
                        swPart.Stop();
                        proc.Refresh();
                        if (!OutputRedirected && !printDebug)
                        {
                            Console.SetCursorPosition(35, Console.GetCursorPosition().Top);
                            Console.Write("100% ");
                        }
                        if (printDebug)
                        {
                            Console.Error.WriteLine();
                            Console.Error.Write(new string(' ', 40));
                        }
                        Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  Total saving {2:##,#} z-chars, text size = {3:##,#} bytes", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), totalSavings, latestTotalBytes);


                        if (printDebug)
                        {
                            Console.Error.WriteLine();
                            if (inform6StyleText)
                                PrintAbbreviationsI6(AbbrevSort(bestCandidateList, false), true);
                            else
                                PrintAbbreviations(AbbrevSort(bestCandidateList, false), gameFilename, true);
                            Console.Error.WriteLine();
                        }
                    }

                    //**********************************************************************************************************************
                    //***** Step 7:  Fast. Try adding and removing intial and trailing spaces  to see if they save bytes by            *****
                    //*****          minimizing the space lost to padding.                                                             *****
                    //**********************************************************************************************************************

                    if (compressionLevel > 0)
                    {
                        // Test if we add/remove initial/trailing space
                        swPart = Stopwatch.StartNew();
                        Console.Error.Write("Add/remove initial/trailing space...".PadRight(40));
                        if (printDebug)
                        {
                            Console.Error.WriteLine();
                            Console.Error.WriteLine();
                        }
                        previousTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);

                        for (int iterations = 1; iterations <= 2; iterations++) // Repeat a couple of times for retesting
                        {
                            int listCount1 = bestCandidateList.Count;
                            for (int i = 0; i < listCount1; i++)
                            {
                                if (bestCandidateList[i].Key.StartsWith(SPACE_REPLACEMENT))
                                {
                                    bestCandidateList[i].Key = bestCandidateList[i].Key[1..];
                                    bestCandidateList[i].Cost -= 1;
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Pass " + iterations + ": replacing " + FormatAbbreviation(SPACE_REPLACEMENT + bestCandidateList[i].Key) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = SPACE_REPLACEMENT + bestCandidateList[i].Key;
                                        bestCandidateList[i].Cost += 1;
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }
                                }
                                else
                                {
                                    bestCandidateList[i].Key = SPACE_REPLACEMENT + bestCandidateList[i].Key;
                                    bestCandidateList[i].Cost += 1;
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Pass " + iterations + ": replacing " + FormatAbbreviation(bestCandidateList[i].Key[1..]) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = bestCandidateList[i].Key[1..];
                                        bestCandidateList[i].Cost -= 1;
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }
                                }
                            }

                            int listCount2 = bestCandidateList.Count;
                            for (int i = 0; i < listCount2; i++)
                            {
                                if (bestCandidateList[i].Key.EndsWith(SPACE_REPLACEMENT))
                                {
                                    bestCandidateList[i].Key = bestCandidateList[i].Key[..^1];
                                    bestCandidateList[i].Cost -= 1;
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Pass " + iterations + ": replacing " + FormatAbbreviation(bestCandidateList[i].Key + SPACE_REPLACEMENT) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = bestCandidateList[i].Key + SPACE_REPLACEMENT;
                                        bestCandidateList[i].Cost += 1;
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }
                                }
                                else
                                {
                                    bestCandidateList[i].Key = bestCandidateList[i].Key + SPACE_REPLACEMENT;
                                    bestCandidateList[i].Cost += 1;
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Pass " + iterations + ": replacing " + FormatAbbreviation(bestCandidateList[i].Key[..^1]) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = bestCandidateList[i].Key[..^1];
                                        bestCandidateList[i].Cost -= 1;
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }
                                }
                            }

                            // Test if we remove initial/trailing character (not only space)
                            int listCount3 = bestCandidateList.Count;
                            for (int i = 0; i < listCount3; i++)
                            {
                                if (bestCandidateList[i].Key.Length > 1)
                                {
                                    string oldCandidate = bestCandidateList[i].Key;
                                    bestCandidateList[i].Key = bestCandidateList[i].Key[1..];
                                    bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Replacing " + FormatAbbreviation(oldCandidate) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = oldCandidate;
                                        bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }

                                    oldCandidate = bestCandidateList[i].Key;
                                    bestCandidateList[i].Key = bestCandidateList[i].Key[..^1];
                                    bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                        {
                                            Console.Error.WriteLine("Replacing " + FormatAbbreviation(oldCandidate) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                        }
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = oldCandidate;
                                        bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }
                                }
                            }

                            // Test if we remove initial/trailing two characters
                            int listCount4 = bestCandidateList.Count;
                            for (int i = 0; i < listCount4; i++)
                            {
                                if (bestCandidateList[i].Key.Length > 2)
                                {
                                    string oldCandidate = bestCandidateList[i].Key;
                                    bestCandidateList[i].Key = bestCandidateList[i].Key[2..];
                                    bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    int deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Replacing " + FormatAbbreviation(oldCandidate) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = oldCandidate;
                                        bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }

                                    oldCandidate = bestCandidateList[i].Key;
                                    bestCandidateList[i].Key = bestCandidateList[i].Key[..^2];
                                    bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                    bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, true, zVersion);
                                    deltaSavings = previousTotalBytes - latestTotalBytes;
                                    if (deltaSavings > 0)
                                    {
                                        // Keep it
                                        previousTotalBytes = latestTotalBytes;
                                        if (printDebug)
                                            Console.Error.WriteLine("Replacing " + FormatAbbreviation(oldCandidate) + " with " + FormatAbbreviation(bestCandidateList[i].Key) + ", saving " + deltaSavings.ToString() + " bytes");
                                    }
                                    else
                                    {
                                        // Restore
                                        bestCandidateList[i].Key = oldCandidate;
                                        bestCandidateList[i].Cost = ZstringCost(bestCandidateList[i].Key);
                                        bestCandidateList[i].UpdateOccurrences(gameTextList, true);
                                    }
                                }
                            }
                        }

                        latestTotalBytes = previousTotalBytes;
                        totalSavings = RescoreOptimalParse(gameTextList, bestCandidateList, false, zVersion);
                        swPart.Stop();
                        proc.Refresh();
                        if (printDebug)
                        {
                            Console.Error.WriteLine();
                            Console.Error.Write(new string(' ', 40));
                        }
                        Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  Total saving {2:##,#} z-chars, text size = {3:##,#} bytes", swPart.ElapsedMilliseconds / 1000.0, proc.PrivateMemorySize64 / (1024 * 1024), totalSavings, latestTotalBytes);

                        if (printDebug)
                        {
                            Console.Error.WriteLine();
                            if (inform6StyleText)
                                PrintAbbreviationsI6(AbbrevSort(bestCandidateList, false), true);
                            else
                                PrintAbbreviations(AbbrevSort(bestCandidateList, false), gameFilename, true);
                            if (customAlphabet) Console.Error.WriteLine();
                        }
                    }
                }

                if (printDebug)
                {
                    Console.Error.WriteLine();
                    if (inform6StyleText)
                        PrintAbbreviationsI6(AbbrevSort(bestCandidateList, false), true);
                    else
                        PrintAbbreviations(AbbrevSort(bestCandidateList, false), gameFilename, true);
                    if (customAlphabet) Console.Error.WriteLine();
                }

                //**********************************************************************************************************************
                //***** Step 8: Finishing up and printing the result                                                               *****
                //**********************************************************************************************************************

                int totalSavingsAlphabet = 0;
                if (!onlyRefactor)
                {
                    if (customAlphabet)
                    {
                        int costDefaultAlphabet = 0;
                        int costCustomAlphabet = 0;

                        foreach (GameText gameTextLine in gameTextList)
                        {
                            costDefaultAlphabet += gameTextLine.costWithDefaultAlphabet;
                            costCustomAlphabet += gameTextLine.costWithCustomAlphabet;
                        }
                        totalSavingsAlphabet = costDefaultAlphabet - costCustomAlphabet;
                        totalSavings += totalSavingsAlphabet;
                        Console.Error.Write("Applying custom alphabet...".PadRight(58));
                        Console.Error.WriteLine("Total saving {0:##,#} z-chars", totalSavings);
                    }
                }

                swTotal.Stop();
                proc.Refresh();
                Console.Error.WriteLine();
                Console.Error.WriteLine("Total elapsed time: {0,7:0.000} s", swTotal.ElapsedMilliseconds / 1000.0);
                Console.Error.WriteLine();

                if (!onlyRefactor)
                {
                    RescoreOptimalParse(gameTextList, bestCandidateList, false, zVersion);
                    totalSavings = 0;
                    int maxAbbrevs = bestCandidateList.Count - 1;
                    if (maxAbbrevs >= NumberOfAbbrevs) maxAbbrevs = NumberOfAbbrevs - 1;
                    for (int i = 0; i <= maxAbbrevs; i++)
                        totalSavings += bestCandidateList[i].Savings;
                    if (customAlphabet)
                        Console.Error.WriteLine(string.Concat("Custom alphabet would save ", totalSavingsAlphabet.ToString("##,#"), " z-chars total (~", Convert.ToInt32(totalSavingsAlphabet * 2 / 3.0).ToString("##,#"), " bytes)"));
                    Console.Error.WriteLine(string.Concat("Abbreviations would save ", totalSavings.ToString("##,#"), " z-chars total (~", Convert.ToInt32(totalSavings * 2 / 3.0).ToString("##,#"), " bytes)"));
                    Console.Error.WriteLine();
                }

                int totalBytes = 0;
                int totalWasted = 0;

                if (!onlyRefactor)
                {
                    // Calculate total cost for storing abbreviations
                    int totalBytesAbbrevs = 0;
                    for (int i = 0; i < NumberOfAbbrevs; i++)
                        totalBytesAbbrevs += 2 * ((bestCandidateList[i].Cost + 2) / 3);

                    // Calculate total cost for strings
                    for (int pass = 0; pass <= 1; pass++)
                    {
                        int[] wasted = new int[12];
                        int[] bytes = new int[12];
                        foreach (GameText line in gameTextList)
                        {
                            if (pass == 0 && line.packedAddress)
                            {
                                wasted[line.latestRoundingCost] += 1;
                                bytes[line.latestRoundingCost] += line.latestTotalBytes;
                            }
                            if (pass == 1 && !line.packedAddress)
                            {
                                wasted[line.latestRoundingCost] += 1;
                                //wasted(line.latestRoundingCost) += 1
                                bytes[line.latestRoundingCost] += line.latestTotalBytes;
                            }
                        }
                        if (pass == 0)
                            Console.Error.WriteLine("High memory strings ({0:##,#} strings):", wasted.Sum());
                        if (pass == 1)
                            Console.Error.WriteLine("Dynamic and static memory strings ({0:##,#} strings):", wasted.Sum());
                        int totalBytesPass = 0;
                        for (var i = 11; i >= 0; i--)
                        {
                            totalBytes += bytes[i];
                            totalBytesPass += bytes[i];
                            totalWasted += wasted[i] * i;
                            if (wasted[i] > 0)
                                Console.Error.WriteLine("{0,6:##,#} strings with {1,2} empty z-chars, total = {2,8:##,0}, {3,7:##,0} bytes", wasted[i], i, wasted[i] * i, bytes[i]);
                        }
                        Console.Error.WriteLine("                                                        -------");
                        Console.Error.WriteLine("                                                        {0,7:##,0} bytes", totalBytesPass);
                    }
                    Console.Error.WriteLine("                                                ===============");
                    Console.Error.WriteLine("Total:                                       {0,9:##,#}, {1,7:##,0} bytes", totalWasted, totalBytes);
                    Console.Error.WriteLine();
                    Console.Error.WriteLine("Storage size for the {0,2} abbreviations:                  {1,7:##,0} bytes", NumberOfAbbrevs, totalBytesAbbrevs);
                    Console.Error.WriteLine("Storage size for the strings:                         + {0,7:##,0} bytes", totalBytes);
                    if (latestTotalPadding > 0)
                        Console.Error.WriteLine("Lost bytes in Z-code padding:                         + {0,7:##,0} bytes", latestTotalPadding);
                    Console.Error.WriteLine("                                                      =========");
                    Console.Error.WriteLine("                                                        {0,7:##,0} bytes", totalBytes + totalBytesAbbrevs + latestTotalPadding);
                    Console.Error.WriteLine();
                }

                if (verbose || onlyRefactor)
                {
                    if (!onlyRefactor)
                    {
                        // High memory strings
                        Console.Error.WriteLine("High memory strings (abbreviations inside {}, ^ = linebreak and ~ = double-quote):");
                        for (int wastedZChars = 11; wastedZChars >= 0; wastedZChars--)
                        {
                            for (var i = 0; i < gameTextList.Count; i++)
                            {
                                if (gameTextList[i].packedAddress && gameTextList[i].latestRoundingCost == wastedZChars)
                                    Console.Error.WriteLine(gameTextList[i].FinishedText(bestCandidateList));
                            }
                        }
                        Console.Error.WriteLine();
                        // Dynamic and static memory strings
                        Console.Error.WriteLine("Dynamic and static memory strings:");
                        for (int wastedZChars = 2; wastedZChars >= 0; wastedZChars--)
                        {
                            for (var i = 0; i < gameTextList.Count; i++)
                            {
                                if (!(gameTextList[i].packedAddress) && gameTextList[i].latestRoundingCost == wastedZChars)
                                    Console.Error.WriteLine(gameTextList[i].FinishedText(bestCandidateList));
                            }
                        }
                        Console.Error.WriteLine();
                    }

                    // Refactoring tips
                    if (maxHeapRefactor.Count > 0)
                    {
                        int totalSavingBytes = 0;
                        int objectDescCount = 0;
                        Console.Error.WriteLine("Long repeated strings:");
                        while (maxHeapRefactor.Count > 0)
                        {
                            PatternData text = maxHeapRefactor.Dequeue();
                            text.UpdateOccurrences(gameTextList, false);
                            int positionInside = 0; // Bit 0=undefined, 1=Equal, 2=starting, 4=ending, 8=inside, 16=includes obj desc
                            for (int i = 0; i < gameTextList.Count; i++)
                            {
                                string gametext = gameTextList[i].text;
                                if (text.Occurrences[i] is not null)
                                {
                                    if (gametext == text.Key) positionInside |= 1;
                                    else if (gametext.StartsWith(text.Key)) positionInside |= 2;
                                    else if (gametext.EndsWith(text.Key)) positionInside |= 4;
                                    else if (gametext.Contains(text.Key)) positionInside |= 8;
                                    if (gameTextList[i].objectDescription) positionInside |= 16;
                                }
                            }
                            string posTxt = "(mixed )";
                            if (positionInside == 1) posTxt = "( full )";
                            if (positionInside == 2) posTxt = "(start )";
                            if (positionInside == 4) posTxt = "( end  )";
                            if (positionInside == 8) posTxt = "(inside)";
                            if ((positionInside & 16) == 16)  posTxt = "(object)";
                            int cost = ZstringCost(text.Key);

                            // Saving (in bytes) are a bit tricky to calculate.
                            // PRINT/print_paddr or PRINTB/print_addr cost 2 bytes when printing from a global variable
                            // and 3 bytes when printing from a direct address in high memory. There's also an extra cost
                            // for space lost to padding when you split up a string to two or three strings (replacing string
                            // inside another string). If one is lucky the padding is zero but it's hard to predict because
                            // new abbreviations are needed afterward. On average splitting a string to two strings will cost
                            // a byte in z1-z3, two bytes in z4-z7 and four bytes in z8. Splitting to three strings double
                            // the padding cost.
                            // In short: this is an estimate based on the string being stored as a constant in high memory
                            // addressed by a direct address (packed or unpacked).
                            int paddingCost = 2; // (mixed), (inside)
                            int splitCost = 6; // (mixed), (inside), assuming direct address, not global
                            if (positionInside == 1) // (full)
                            {
                                paddingCost = 0;
                                splitCost = 0;
                            }
                            else if (positionInside == 2 || positionInside == 4 || positionInside == 6) // (start), (end)
                            {
                                paddingCost = 1;
                                splitCost = 3; // assuming direct address, not global
                            }
                            if (zVersion > 3) paddingCost *= 2;
                            if (zVersion > 7) paddingCost *= 2;
                            int savingInBytes = Convert.ToInt32(Math.Ceiling(((text.Frequency - 1 - objectDescCount) * cost) * 2 / 3.0)) - splitCost * (text.Frequency - 1 - objectDescCount) - paddingCost;
                            if (savingInBytes > 0)
                            {
                                Console.Error.WriteLine("{0,3}x{1,3} z-chars (~ {2,3} bytes), {3} {4}{5}{6}", text.Frequency - objectDescCount, cost, savingInBytes, posTxt, (char)34, text.Key.Replace(SPACE_REPLACEMENT.ToString(), " ").Replace(LF_REPLACEMENT, '^'), (char)34);
                                totalSavingBytes += savingInBytes;
                            }
                        }
                        Console.Error.WriteLine();
                    }
                }

                if (!onlyRefactor)
                {
                    // Print result
                    if (customAlphabet)
                    {
                        if (inform6StyleText)
                            PrintAlphabetI6();
                        else
                            PrintAlphabet();
                    }
                    if (inform6StyleText)
                        PrintAbbreviationsI6(AbbrevSort(bestCandidateList, false), false);
                    else
                        PrintAbbreviations(bestCandidateList, gameFilename, false);
                }

#if STOPWATCH
                if (stopwatches)
                {
                    Console.Error.WriteLine();
                    Console.Error.WriteLine("Total elapsed time:                           {0,7:0.000} s", swTotal.ElapsedMilliseconds / 1000.0);
                    Console.Error.WriteLine("Stopwatch 1, RescoreOptimalParse:             {0,7:0.000} s, {1:##,0} calls", sw1.ElapsedMilliseconds / 1000.0, callCount);
                    Console.Error.WriteLine("Stopwatch 2:    Clear frequencies:            {0,7:0.000} s", sw2.ElapsedMilliseconds / 1000.0);
                    Console.Error.WriteLine("Stopwatch 3:    Create abbreviationLocations: {0,7:0.000} s", sw3.ElapsedMilliseconds / 1000.0);
                    Console.Error.WriteLine("Stopwatch 4:    Abbreviation optimization:    {0,7:0.000} s", sw4.ElapsedMilliseconds / 1000.0);
                    Console.Error.WriteLine("Stopwatch 5:    Update frequencies:           {0,7:0.000} s", sw5.ElapsedMilliseconds / 1000.0);
                }
#endif
            }
            catch (Exception ex)
            {
                Console.Error.WriteLine("ERROR: ZAbbrev failed.");
                Console.Error.WriteLine(ex.Message);
            }
        }

        public class PatternComparer : IComparer<int>
        {
            public int Compare(int x, int y)
            {
                // Here we compare this instance with other.
                // If this is supposed to come before other once sorted then
                // we should return a negative number.
                // If they are the same, then return 0.
                // If this one should come after other then return a positive number.
                if (x > y) return -1;
                if (x < y) return 1;
                return 0;
            }
        }

        public class GameText
        {
            public int costWithDefaultAlphabet = 0;
            public int costWithCustomAlphabet = 0;
            public int latestMinimalCost = 0;
            public int latestRoundingCost = 0;
            public int latestTotalBytes = 0;
            public int[] pickedAbbreviations;
            public int[] suffixArray;
            public int[] lcpArray;
            public bool packedAddress = false;
            public bool objectDescription = false;
            public int[] minimalCostFromHere; // Temporary array for holdinmgh Wagner's 'f' or 'F' during calculation
            public int routineID = -1;

            public GameText(string value)
            {
                this.text = value;
                // Init size of arrays once and for all to avoid dynamic allocation in RescoreOptimalParse
                minimalCostFromHere = new int[this.TextAsSpan.Length + 2];
                minimalCostFromHere[this.TextAsSpan.Length] = 0;
                pickedAbbreviations = new int[this.TextAsSpan.Length + 1];
            }

            public readonly string text = "";

            private char[] _textAsSpan = null;
            public ReadOnlySpan<char> TextAsSpan
            {
                get
                {
                    _textAsSpan??=text.ToCharArray();
                    return _textAsSpan;
                }
            }

            public string FinishedText(List<PatternData> abbreviations)
            {
                for (int i = 0; i < this.text.Length; i++)
                {
                    // Clean the pickedAbbreviations array from all overlapped (false) abbreviations.
                    if (pickedAbbreviations[i] > -1)
                    {
                        Array.Fill(pickedAbbreviations, -1, i + 1, abbreviations[pickedAbbreviations[i]].Length - 1);
                        i += abbreviations[pickedAbbreviations[i]].Length - 1; // Skip to next slot after abbreviation
                    }
                }

                // Construct actual string with abbreviations inside {}
                string returnText = this.text;
                for (int i = returnText.Length - 1; i >= 0; i--)
                {
                    if (pickedAbbreviations[i] > -1)
                    {
                        string abbreviation = abbreviations[pickedAbbreviations[i]].Key;
                        returnText = returnText[..i] + "{" + abbreviation + "}" + returnText[(i + abbreviation.Length)..];
                    }
                }
                returnText = string.Format("{0,3} z-chars + {1} unused slot(s) = {2,3} bytes: {3}{4}{5}", latestMinimalCost, latestRoundingCost, latestTotalBytes, (char)34, returnText.Replace(SPACE_REPLACEMENT.ToString(), " ").Replace(LF_REPLACEMENT, '^'), (char)34);
                return returnText;
            }

        }
        public class PatternData
        {
            public string Key = "";
            public int Frequency = 0;
            public int Cost = 0;
            public int Savings = 0;
            public bool locked = false;
            public List<int>[] Occurrences = null;
            public int lineOfFirstOccurrence = -1;
            public HashSet<string> textLines = null;
            public int Length;

            public int Score
            {
                get
                {
                    // The total savings for the abbreviation
                    // 2 is the cost in zchars for the link to the abbreviation
                    // The abbreviation also need to be stored once and that
                    // requires the cost rounded up the nearest number 
                    // dividable by 3 (3 zhars per word).
                    return (Frequency * (Cost - 2)) - ((Cost + 2) / 3) * 3;
                }
            }

            public PatternData Clone()
            {
                return (PatternData)this.MemberwiseClone();
            }

            public void UpdateOccurrences(List<GameText> gameTextList, bool forceRecalc = false)
            {
                if (Occurrences is null || forceRecalc)
                {
                    Occurrences = new List<int>[gameTextList.Count + 1];
                    for (int row = 0; row < gameTextList.Count; row++)
                    {
                        int col = gameTextList[row].text.IndexOf(this.Key, StringComparison.Ordinal);
                        while (col >= 0)
                        {
                            if (Occurrences[row] is null) Occurrences[row] = [];
                            Occurrences[row].Add(col);
                            col = gameTextList[row].text.IndexOf(this.Key, col + 1, StringComparison.Ordinal);
                        }
                    }
                }
            }
        }

        private static byte ASCII(char cChr)
        {
            return (byte)cChr;
        }

        private static int ZstringCost(string sText)
        {
            int iCost = 0;
            for (int i = 0; i < sText.Length; i++)
                iCost += ZcharCost(sText[i]);
            return iCost;
        }

        private static int ZcharCost(char zchar)
        {
            // Among String, HashSet & Span, HashSet is the fastest for "contains"
            if (alphabet0Hash.Contains(zchar)) return 1;      // Alphabet A0 and space
            if (alphabet1And2Hash.Contains(zchar)) return 2;  // Alphabet A1, A2, quote (") And linefeed
            return 4;
        }

        private static int RescoreOptimalParse(List<GameText> gameText, List<PatternData> abbreviations, bool returnTotalBytes, int zversion)
        {
            // Parse string using Wagner's optimal parse
            // Almost all execution time is spent in here calculation. Optimization for speed is of ESSENCE!
            //   - ~96.5% of execution time is in this function 
            // https://ecommons.cornell.edu/server/api/core/bitstreams/b2f394c1-f11d-4200-b2d4-1351aa1d12ab/content
            // https://dl.acm.org/doi/pdf/10.1145/361972.361982

#if STOPWATCH
            if (stopwatches)
            {
                sw1.Start();
                callCount += 1;
            }
#endif

            // Clear frequency from abbrevs and init occurences of this abbreviation if it's not done yet.
            // Optimization info: ~1.7% of total time here
#if STOPWATCH
            if (stopwatches) sw2.Start();
#endif
            foreach (PatternData abbreviation in abbreviations)
            {
                abbreviation.Frequency = 0;
                abbreviation.Length = abbreviation.Key.Length; // Init abbreviation length
                abbreviation.UpdateOccurrences(gameText, false);
            }
#if STOPWATCH
            if (stopwatches) sw2.Stop();
#endif
            int totalBytes = 0;

            // Iterate over each string and pick optimal set of abbreviations from abbrevs for this string
            for (int line = 0; line < gameText.Count; line++)
            {
                GameText gameTextLine = gameText[line];
                int lengthOfTextLine = gameTextLine.TextAsSpan.Length; // Cache length

#if STOPWATCH
                if (stopwatches) sw3.Start();
#endif
                // Generate an array, length of this textline, with lists that of each possible
                // abbreviation from current collection of abbreviations.
                // List is null = no possible abbreviations at this position.
                // Optimization info: ~41.8% of total time here
                List<int>[] possibleAbbrevsArray = new List<int>[lengthOfTextLine];
                for (int abbrevNo = 0; abbrevNo < abbreviations.Count; abbrevNo++)
                {
                    List<int> abbrevOccurrences = abbreviations[abbrevNo].Occurrences[line];
                    if (abbrevOccurrences is not null)
                    {
                        for (int abbrevPosition = 0; abbrevPosition < abbrevOccurrences.Count; abbrevPosition++)
                        {
                            if (possibleAbbrevsArray[abbrevOccurrences[abbrevPosition]] is null)
                                possibleAbbrevsArray[abbrevOccurrences[abbrevPosition]] = new List<int>(1);  // initiate list with 1 slot (most common). Curses max out at 4.
                            possibleAbbrevsArray[abbrevOccurrences[abbrevPosition]].Add(abbrevNo);
                        }
                    }
                }
#if STOPWATCH
                if (stopwatches) sw3.Stop();
#endif

#if STOPWATCH
                if (stopwatches) sw4.Start();
#endif
                // Iterate reverse over this textline and apply the abbreviation for each position that is
                // most effective (optimal parse).
                // Optimization info: ~40.0% of total time here
                var minimalCostFromHere = gameTextLine.minimalCostFromHere;   // Use local copy to hopefully avoid boundary check
                var pickedAbbreviations = gameTextLine.pickedAbbreviations;   // Use local copy to hopefully avoid boundary check
                Array.Fill(pickedAbbreviations, -1);                          // -1 for "no abbreviation"
                for (int index = lengthOfTextLine - 1; index >= 0; index--)
                {
                    minimalCostFromHere[index] = minimalCostFromHere[index + 1] + ZcharCost(gameTextLine.TextAsSpan[index]);
                    if (possibleAbbrevsArray[index] is not null)
                    {
                        foreach (int abbrevNo in possibleAbbrevsArray[index])
                        {
                            int costWithPattern = ABBREVIATION_REF_COST + minimalCostFromHere[index + abbreviations[abbrevNo].Length];

                            // If using the abbreviation saves z-chars, then use it
                            if (costWithPattern < minimalCostFromHere[index])
                            {
                                pickedAbbreviations[index] = abbrevNo;
                                minimalCostFromHere[index] = costWithPattern;
                            }

                            // 1. If cost for using the z-char is equal to the use of the abbreviation, then use the z-char.
                            // 2. If two abbreviations equals the same minimal cost, use the one that represents most
                            //    z-chars (usually the longest).
                            // 3. If the two abbreviations also have the same number of z-chars, use the one that's last defined.
                            if (!(pickedAbbreviations[index] == -1) && costWithPattern == minimalCostFromHere[index] && abbreviations[abbrevNo].Cost >= abbreviations[gameTextLine.pickedAbbreviations[index]].Cost)
                            {
                                pickedAbbreviations[index] = abbrevNo;
                                minimalCostFromHere[index] = costWithPattern;
                            }

                        }
                    }
                }
#if STOPWATCH
                if (stopwatches) sw4.Stop();
#endif

#if STOPWATCH
                if (stopwatches) sw5.Start();
#endif
                // Update frequencies for picked abbreviations. Iterate from front so only actally used
                // abbreviations gets updated.
                // Note that the pickedAbbreviations array now also contains overlapped (false) abbreviations.
                // These will be removed in the GameText.FinishedText method before printing string.  
                // Optimization info: ~10.2% of total time here
                for (int index = 0; index < lengthOfTextLine; index++)
                {
                    if (pickedAbbreviations[index] > -1)
                    {
                        abbreviations[pickedAbbreviations[index]].Frequency += 1;
                        index += abbreviations[pickedAbbreviations[index]].Length - 1; // Skip to next slot after abbreviation
                    }
                }
#if STOPWATCH
                if (stopwatches) sw5.Stop();
#endif
                // Aggregate rounding penalty for each textline.
                // zchars are 5 bits and are stored in words (16 bits), 3 in each word. 
                // Depending on rounding 0, 1 or 2 slots can be "wasted" here.
                // Depending on version waste can also be up to 5 or 11 slots for high strings. Inline strings
                // always have rounding of 3 inside routines (between routines the waste can be bigger because
                // of padding but that is ignored here). 
                // Optimization info: ~6.3% of total time here (to end)
                var roundingNumber = 3;
                if (gameTextLine.packedAddress)
                {
                    if (zversion > 3) roundingNumber = 6;
                    if (zversion == 8) roundingNumber = 12;
                }
                gameTextLine.latestRoundingCost = (roundingNumber - (minimalCostFromHere[0] % roundingNumber)) % roundingNumber;
                gameTextLine.latestMinimalCost = minimalCostFromHere[0];
                gameTextLine.latestTotalBytes = ((gameTextLine.latestMinimalCost + gameTextLine.latestRoundingCost) * 2) / 3;
                totalBytes += gameTextLine.latestTotalBytes;
            }

            // Summmarize savings and bytes for picked abbreviations.
            int totalSavings = 0;
            foreach (PatternData abbrev in abbreviations)
            {
                abbrev.Savings = abbrev.Score;
                totalSavings += abbrev.Savings;
                totalBytes += 2 * ((abbrev.Cost + 2) / 3); // Add cost for storing abbreviations
            }

            // 0.11: Add padding cost from z-code routines, if available
            int totalPadding = 0;
            if (returnTotalBytes)
            {
                int latestStartIndex = 0;
                for (var i = 0; i < routineSize.Count; i++)
                {
                    int routineSizeInBytes = routineSize[i];
                    for (var j = latestStartIndex; j < gameText.Count; j++)
                    {
                        if (gameText[j].routineID > i)
                        {
                            latestStartIndex = j;
                            break;
                        }
                        if (gameText[j].routineID == i) routineSizeInBytes += gameText[j].latestTotalBytes;
                    }
                    if (zversion < 4 && (routineSizeInBytes & 1) == 1) // Version 1-3, If routines size is odd then add one byte for padding
                        totalPadding += 1;
                    if (zversion > 3 && zversion < 8)                  // Version 4-7, padding is number of bytes until divisible by 4
                        totalPadding += (4 - (routineSizeInBytes % 4)) % 4;
                    if (zversion == 8)                                 // Version 8, padding is number of bytes until divisible by 8
                        totalPadding += (8 - (routineSizeInBytes % 8)) % 8;
                }
                latestTotalPadding = totalPadding;
            }

#if STOPWATCH
            sw1.Stop();
#endif

            // Return result
            if (returnTotalBytes)
                return totalBytes + totalPadding;
            else
                return totalSavings;
        }

        private static List<PatternData> AbbrevSort(List<PatternData> abbrevList, bool sortByFrequency)
        {
            List<PatternData> returnList = [];
            for (int i = 0; i < NumberOfAbbrevs; i++)
            {
                returnList.Add(abbrevList[i].Clone());
            }

            if (sortByFrequency)
            {
                returnList.Sort((PatternData firstPair, PatternData nextPair) => Convert.ToInt32(firstPair.Frequency).CompareTo(Convert.ToInt32(nextPair.Frequency)));
                returnList.Reverse();

                for (int i = NumberOfAbbrevs; i < abbrevList.Count; i++)
                    returnList.Add(abbrevList[i].Clone());
            }
            else
            {
                returnList.Sort((PatternData firstPair, PatternData nextPair) => ((int)firstPair.Key.Length).CompareTo((int)nextPair.Key.Length));
                returnList.Reverse();

                for (int i = NumberOfAbbrevs; i < abbrevList.Count; i++)
                    returnList.Add(abbrevList[i].Clone());
            }

            return returnList;
        }

        private static string PrintFormattedAbbreviation(int abbreviationNo, string abbreviation, int frequency, int score, int cost)
        {
            int padExtra = 0;
            if (abbreviationNo < 10)
                padExtra = 1;
            return string.Concat("        .FSTR FSTR?", abbreviationNo.ToString(), ",", FormatAbbreviation(abbreviation).PadRight(20 + padExtra), "; ", frequency.ToString().PadLeft(4), "x", cost, ", saved ", score);
        }

        private static string FormatAbbreviation(string abbreviation)
        {
            return string.Concat((char)34, abbreviation.Replace(SPACE_REPLACEMENT.ToString(), " ").Replace(QUOTE_REPLACEMENT, '"').Replace(LF_REPLACEMENT, '\n'), (char)34);
        }

        private static void PrintAbbreviations(List<PatternData> abbrevList, string gameFilename, bool toError)
        {
            System.IO.TextWriter outStream = Console.Out;
            if (toError) outStream = Console.Error;

            outStream.WriteLine("        ; Frequent words file for {0}", gameFilename);
            outStream.WriteLine();

            int max = NumberOfAbbrevs - 1;
            if (abbrevList.Count < max + 1) max = abbrevList.Count - 1;
            for (int i = 0; i <= max; i++)
                outStream.WriteLine(string.Concat(PrintFormattedAbbreviation(i + 1, abbrevList[i].Key, abbrevList[i].Frequency, abbrevList[i].Score, abbrevList[i].Cost)));

            outStream.WriteLine("WORDS::");

            for (int i = 0; i <= max; i++)
                outStream.WriteLine("        FSTR?{0}", i + 1);

            outStream.WriteLine();
            outStream.WriteLine("        .ENDI");
        }

        private static void PrintAbbreviationsI6(List<PatternData> abbrevList, bool toError)
        {
            System.IO.TextWriter outStream = Console.Out;
            if (toError) outStream = Console.Error;

            int max = NumberOfAbbrevs - 1;
            if (abbrevList.Count < max + 1) max = abbrevList.Count - 1;
            for (int i = 0; i <= max; i++)
            {
                string line = abbrevList[i].Key;
                line = line.Replace(SPACE_REPLACEMENT.ToString(), " ");
                line = line.Replace(LF_REPLACEMENT.ToString(), "^");
                line = line.Replace("~", QUOTE_REPLACEMENT.ToString());
                int spaces = 30 - line.Length;
                string warningText = "";
                if (line.Length > 64)
                    warningText = " Warning: Abbreviation too long. Inform6 limits abbreviationas to max 64 characters.";
                if (spaces < 0) spaces = 0;
                outStream.WriteLine(string.Concat("Abbreviate ", (char)34, line, (char)34, ";", new string(' ', spaces), "! ", abbrevList[i].Frequency.ToString().PadLeft(5), "x", abbrevList[i].Cost.ToString().PadLeft(2), ", saved ", abbrevList[i].Score.ToString().PadLeft(5), warningText));
            }
        }

        private static bool IsFileUTF8(string fileName)
        {
            System.Text.DecoderExceptionFallback FallbackExp = new();

            byte[] fileBytes = System.IO.File.ReadAllBytes(fileName);
            var decoderUTF8 = System.Text.Encoding.UTF8.GetDecoder();
            decoderUTF8.Fallback = FallbackExp;
            bool IsUTF8;
            try
            {
                int charCount = decoderUTF8.GetCharCount(fileBytes, 0, fileBytes.Length);
                IsUTF8 = true;
            }
            catch
            {
                IsUTF8 = false;
            }

            return IsUTF8;
        }

        private static string SortAlphabet(string alphabetIn, string AlphabetOrg)
        {
            char[] alphaArray = new char[AlphabetOrg.Length];
            for (int i = 0; i < alphaArray.Length; i++)
            {
                if (alphabetIn.Contains(AlphabetOrg.Substring(i, 1), StringComparison.Ordinal))
                    alphaArray[i] = char.Parse(AlphabetOrg.Substring(i, 1));
                else
                    alphaArray[i] = ' ';
            }
            int arrayLength = alphaArray.Length;
            for (int i = 0; i < arrayLength; i++)
            {
                if (!((new string(alphaArray)).Contains(alphabetIn.Substring(i, 1), StringComparison.Ordinal)))
                {
                    for (int j = 0; j < alphaArray.Length; j++)
                    {
                        if (alphaArray[j] == ' ')
                        {
                            alphaArray[j] = char.Parse(alphabetIn.Substring(i, 1));
                            break;
                        }
                    }
                }
            }
            return new string(alphaArray);
        }

        private static void PrintAlphabet()
        {
            Console.Out.WriteLine(";" + (char)34 + "Custom-made alphabet. Insert at beginning of game file." + (char)34);
            Console.Out.WriteLine(";" + (char)34 + "(Note! Custom-made alphabet are only defined for versions 5 onward." + (char)34);
            Console.Out.WriteLine(";" + (char)34 + "       Intrepreters may or may not accept it in earlier versions." + (char)34);
            Console.Out.WriteLine(";" + (char)34 + "       (see Z-Machine Standards Document, §3.5.5.))" + (char)34);
            Console.Out.WriteLine("<CHRSET 0 " + (char)34 + alphabet0 + (char)34 + ">");
            Console.Out.WriteLine("<CHRSET 1 " + (char)34 + alphabet1 + (char)34 + ">");
            // A2, pos 0 - always escape to 10 bit characters
            // A2, pos 1 - always newline
            // A2, pos 2 - insert doublequote (as in Inform6)
            Console.Out.WriteLine("<CHRSET 2 " + (char)34 + "\\" + (char)34 + alphabet2 + (char)34 + ">");
            Console.Out.WriteLine();
        }

        private static void PrintAlphabetI6()
        {
            Console.Out.WriteLine("! Custom-made alphabet. Insert at beginning of game file (see DM4, §36).");
            Console.Out.WriteLine("! (Note! Custom-made alphabet are only defined for versions 5 onward.");
            Console.Out.WriteLine("!        Intrepreters may or may not accept it in earlier versions.");
            Console.Out.WriteLine("!        (see Z-Machine Standards Document, §3.5.5.))");
            Console.Out.WriteLine("Zcharacter");
            Console.Out.WriteLine("    " + (char)34 + alphabet0.Replace("@", "@{0040}").Replace("\\", "@{005C}") + (char)34);
            Console.Out.WriteLine("    " + (char)34 + alphabet1.Replace("@", "@{0040}").Replace("\\", "@{005C}") + (char)34);
            // A2, pos 0 - always escape to 10 bit characters
            // A2, pos 1 - always newline
            // A2, pos 2 - always doublequote
            Console.Out.WriteLine("    " + (char)34 + alphabet2.Replace("@", "@{0040}").Replace("\\", "@{005C}") + (char)34 + ";");
            Console.Out.WriteLine();
        }

        private static DateTime GetBuildDateUtc(Assembly assembly)
        {
            const string BuildVersionMetadataPrefix = "+build";

            var attribute = assembly.GetCustomAttribute<AssemblyInformationalVersionAttribute>();
            if (attribute?.InformationalVersion != null)
            {
                var value = attribute.InformationalVersion;
                var index = value.IndexOf(BuildVersionMetadataPrefix);
                if (index > 0)
                {
                    value = value[(index + BuildVersionMetadataPrefix.Length)..];
                    if (DateTime.TryParseExact(value, "yyyyMMddHHmmss", CultureInfo.InvariantCulture, DateTimeStyles.None, out var result))
                    {
                        return result;
                    }
                }
            }

            return default;
        }
    }

}
