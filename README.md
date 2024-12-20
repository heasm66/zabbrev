# zabbrev
Tool to make better abbreviations for ZIL and the z-machine. Input is the zap-files that results from compiling the zil-files. Typical workflow for Zilf:

    zilf.exe game.zil
    del game_freq.zap
    zabbrev.exe > game_freq.xzap
    zapf.exe game.zap
    
Typical workflow for Inform6 (be sure that your gamefile includes the file abbrevs.h or paste in them directly in the gamefile):

    inform6 -r $TRANSCRIPT_FORMAT=1 <game-path>\<game>.inf
    zabbrev.exe -i > abbrevs.h
    inform6 -e $MAX_ABBREVS=96 <game-path>\<game>.inf
    
Precompiled binaries are at: https://drive.google.com/drive/folders/1At6RU4wei5qwoF3dchVMZuW2MsT2IPhI

## Instructions

    ZAbbrev 0.11 (2024-11-29 11:34:21) by Henrik Åsman, (c) 2021-2024
    Usage: zabbrev [switches] [path-to-game]
    Highly optimized abbreviations computed efficiently

     -a                 Create a tailor-made alphabet for this game and use it as basis for
                        the abbreviations (z5+ only).
     -a0 <string>       Define 26 characters for alphabet A0.
     -a1 <string>       Define 26 characters for alphabet A1.
     -a2 <string>       Define 23 characters for alphabet A2.
                        Experimental - works best when text encoding is in ISO-8859-1 (C0 or C1).
     -b                 Throw all abbreviations that have lower score than last pick back on heap.
                        (This only occasionally improves the result, use sparingly.)
     -c0                Text character set is plain ASCII only.
     -cu                Text character set is UTF-8.
     -c1                Text character set is ISO 8859-1 (Latin1, ANSI).
     --debug            Prints debug information.
     -i                 The switch is redundant (it will be auto-detected if 'gametext.txt' is in the gamepath).
                        Generate output for Inform6. This requires that the file.
                        'gametext.txt' is in the gamepath. 'gametext.txt' is generated by:
                           inform6 -r $TRANSCRIPT_FORMAT=1 <game>.inf
                        in Inform6 version 6.35 or later. -i always use -r3.
     --infodump <file>  Use text extracted from a compiled file with the ZTool, Infodump.
                        The file is generated by:
                           infodump -io <game> > <game>.infodump
                        (Always used in conjunction with the -txd switch.)
     -n nn              # of abbreviations to generate (default = 96).
     -o 0/input         Output abbreviations in format as the input source (default).
        1/inform        Output abbreviations in Inform6 format.
        2/ZAP           Output abbreviations in ZAP format.
     --onlyrefactor     Skip calculation of abbrevations and only print information about duplicate long strings.
     -r3                Always round to 3 for fast and deep rounding. Normally rounding
                        to 6 is used for strings stored in high memory for z4+ games.
     --stopwatches      Print detailed timing information on function RescoreOptimalParse. For debugging purposes only.
     --txd <file>       Use text extracted from a compiled file with the ZTool, Txd.
                        The file is generated by:
                           txd -ag <game> > <game>.txd
                        (Always used in conjunction with the -infodump switch.)
     -v1 - v8           Z-machine version. 1-3: Round to 3 for high strings
                                           4-7: Round to 6 for high strings
                                             8: Round to 12 for high strings
     -v                 Verbose. Prints extra information.
     -x0                Compression level 0, fastest.
                        Pick abbreviations according to highest score with R.A. Wagner's 'Optimal Parse' method.
     -x1                Compression level 1, fast.
                        x0 and adding and removing initial and trailing characters for better z-chars rounding.
     -x2 [n]            Compression level 2, normal. (default)
                        x1 and testing up to n (default n = 10 000) discarded abbreviation variants for better z-chars rounding.
     -x3 [n1] [n2]      Compression level 3, maximum.
                        x2 and testing n2 (default n1 = 10 000, n2 = 1 000) discarded abbreviations as all possible replacements
                        for better z-chars rounding.
     path-to-game       Use this path. If omitted the current path is used.
    
## References
### Algorithm
https://intfiction.org/t/highly-optimized-abbreviations-computed-efficiently/48753  
https://intfiction.org/t/playable-version-of-mini-zork-ii/49326
https://gitlab.com/russotto/zilabbrs  
https://github.com/hlabrand/retro-scripts  
### RA Wagner's Optimal Parse
https://ecommons.cornell.edu/server/api/core/bitstreams/b2f394c1-f11d-4200-b2d4-1351aa1d12ab/content
https://dl.acm.org/doi/pdf/10.1145/361972.361982
### Suffix Array
https://www.geeksforgeeks.org/suffix-array-set-2-a-nlognlogn-algorithm/
https://www.geeksforgeeks.org/kasais-algorithm-for-construction-of-lcp-array-from-suffix-array/?ref=ml_lbp
https://stackoverflow.com/questions/57748988/kasai-algorithm-for-constructing-lcp-array-practical-example
