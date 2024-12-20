
'Copyright (C) 2021, 2023 Henrik Åsman
'You can redistribute and/or modify this file under the terms of the
'GNU General Public License as published by the Free Software
'Foundation, either version 3 of the License, or (at your option) any
'later version.
'This file is distributed in the hope that it will be useful, but
'WITHOUT ANY WARRANTY; without even the implied warranty of
'MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
'General Public License for more details.
'You should have received a copy of the GNU General Public License
'along with this file. If not, see <https://www.gnu.org/licenses/>."

' TODO:
'   * Convert to C# (converter.telerik.com)
'   * When C#, use Span instead of Array
'   * Add output option to UnZil for a gametext.txt-file
'   * Optimization for pass 2, use suffix array?
'   * Find better algorithm for viable patterns to test in pass 2
'   * Refactoring tip: suggest beginning or end of text globals (".^" = PERIOD-CR)
'   * Switch to export ZIL alphabet in ZAP-format (so a bat-script can pipe it in automatically)

' Changelog:
' 0.8  2022-01-15 Visual Studio 2019, NET5.0
' 0.9  2023-08-11 Visual Studio 2022, NET7 (3x faster then earlier version)
'                 Using new features when publishing
'                 Small optimizations
' 0.10 2024-01-10 Visual Studio 2022, NET8
'                 Using Suffix Array for optimizations (2x faster then earlier version)
'                 New output/statistics

Imports System

Module Program
    Public Const NUMBER_OF_ABBREVIATIONS As Integer = 96
    Public Const SPACE_REPLACEMENT As Char = CChar("^")
    Public Const QUOTE_REPLACEMENT As Char = CChar("~")
    Public Const LF_REPLACEMENT As Char = CChar("|")
    Public Const ABBREVIATION_REF_COST As Integer = 2 ' An abbreviation reference Is 2 characters, 
    Public Const NUMBER_OF_PASSES As Integer = 10000
    Public Const CUTOFF_LONG_PATTERN As Integer = 20

    Private ReadOnly defaultA0 As String = "abcdefghijklmnopqrstuvwxyz"
    Private ReadOnly defaultA1 As String = "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
    Private ReadOnly defaultA2 As String = "0123456789.,!?_#'/\-:()"     ' 3 slots are reserved for an escape char, newline and doublequote
    Private customAlphabet As Boolean = False
    Private alphabet0 As String = defaultA0
    Private alphabet1 As String = defaultA1
    Private alphabet2 As String = defaultA2
    Private ReadOnly alphabet0Hash As New HashSet(Of Char)
    Private ReadOnly alphabet1And2Hash As New HashSet(Of Char)
    Private OutputRedirected As Boolean = False
    Private zVersion As Integer = 0
    Private tryAutoDetectZVersion As Boolean = False
    Private Property NumberOfAbbrevs As Integer = NUMBER_OF_ABBREVIATIONS
    Private Property TextEncoding As System.Text.Encoding = Nothing

    Private infodumpFilename As String = ""
    Private txdFilename As String = ""

    Private verbose As Boolean = False
    Private onlyRefactor As Boolean = False

    Sub Main(args As String())
        Dim forceRoundingTo3 As Boolean = False
        Dim printDebug As Boolean = False
        Dim throwBackLowscorers As Boolean = False
        Dim fastRounding As Boolean = True
        Dim deepRounding As Boolean = True
        Dim fastBeforeDeep As Boolean = False
        Dim inform6StyleText As Boolean = False
        Dim gameDirectory As String = Environment.CurrentDirectory

        ' Parse arguments
        For i As Integer = 0 To args.Length - 1
            Select Case args(i)
                Case "-a"
                    customAlphabet = True
                Case "-a0"
                    If i < args.Length - 1 AndAlso args(i + 1).Length = 26 Then
                        alphabet0 = args(i + 1)
                        i += 1
                    Else
                        Console.Error.WriteLine("WARNING: Can't use defined A0 (needs 26 characters). Using defailt instead.")
                    End If
                Case "-a1"
                    If i < args.Length - 1 AndAlso args(i + 1).Length = 26 Then
                        alphabet1 = args(i + 1)
                        i += 1
                    Else
                        Console.Error.WriteLine("WARNING: Can't use defined A1 (needs 26 characters). Using defailt instead.")
                    End If
                Case "-a2"
                    If i < args.Length - 1 AndAlso args(i + 1).Length = 23 Then
                        alphabet2 = args(i + 1)
                        i += 1
                    Else
                        Console.Error.WriteLine("WARNING: Can't use defined A2 (needs 23 characters). Using defailt instead.")
                    End If
                Case "-r3"
                    forceRoundingTo3 = True
                Case "-v"
                    verbose = True
                Case "--debug"
                    printDebug = True
                Case "-b"
                    throwBackLowscorers = True
                Case "-f"
                    fastRounding = True
                    deepRounding = False
                Case "-d"
                    fastRounding = False
                    deepRounding = True
                Case "-df"
                    fastRounding = True
                    deepRounding = True
                    fastBeforeDeep = False
                Case "-fd"
                    fastRounding = True
                    deepRounding = True
                    fastBeforeDeep = True
                Case "-n"
                    If i < args.Length - 1 AndAlso Integer.TryParse(args(i + 1), NumberOfAbbrevs) Then
                        i += 1
                    End If
                Case "-h", "--help", "\?"
                    Console.Error.WriteLine("ZAbbrevMaker 0.10")
                    Console.Error.WriteLine("ZAbbrevMaker [switches] [path-to-game]")
                    Console.Error.WriteLine()
                    Console.Error.WriteLine(" -a                 Create a tailor-made alphabet for this game and use it as basis for")
                    Console.Error.WriteLine("                    the abbreviations (z5+ only).")
                    Console.Error.WriteLine(" -a0 <string>       Define 26 characters for alphabet A0.")
                    Console.Error.WriteLine(" -a1 <string>       Define 26 characters for alphabet A1.")
                    Console.Error.WriteLine(" -a2 <string>       Define 23 characters for alphabet A2.")
                    Console.Error.WriteLine("                    Experimental - works best when text encoding is in ISO-8859-1 (C0 or C1).")
                    Console.Error.WriteLine(" -b                 Throw all abbreviations that have lower score than last pick back on heap.")
                    Console.Error.WriteLine("                    (This only occasionally improves the result, use sparingly.)")
                    Console.Error.WriteLine(" -c0                Text character set is plain ASCII only.")
                    Console.Error.WriteLine(" -cu                Text character set is UTF-8.")
                    Console.Error.WriteLine(" -c1                Text character set is ISO 8859-1 (Latin1, ANSI).")
                    Console.Error.WriteLine(" --debug            Prints debug information.")
                    Console.Error.WriteLine(" -d                 Deep rounding. Try up yo 10,000 variants from discarded abbreviations")
                    Console.Error.WriteLine("                    and see if it gives better savings on account of z-chars rounding.")
                    Console.Error.WriteLine(" -df                Try deep rounding and then fast rounding, in that order (default).")
                    Console.Error.WriteLine(" -f                 Fast rounding. Try variants (add remove space) to abbreviations")
                    Console.Error.WriteLine("                    and see if it gives better savings on account of z-chars rounding.")
                    Console.Error.WriteLine(" -fd                Try fast rounding and then deep rounding, in that order.")
                    Console.Error.WriteLine(" -i                 The switch is deprecated (it will auto-detected)")
                    Console.Error.WriteLine("                    Generate output for Inform6. This requires that the file.")
                    Console.Error.WriteLine("                    'gametext.txt' is in the gamepath. 'gametext.txt' is generated by:")
                    Console.Error.WriteLine("                       inform6 -r $TRANSCRIPT_FORMAT=1 <game>.inf")
                    Console.Error.WriteLine("                    in Inform6 version 6.35 or later. -i always use -r3.")
                    Console.Error.WriteLine(" --infodump <file>  Use text extracted from a compiled file with the ZTool, Infodump.")
                    Console.Error.WriteLine("                    The file is generated by:")
                    Console.Error.WriteLine("                       infodump -io <game> > <game>.infodump")
                    Console.Error.WriteLine("                    (Always used in conjunction with the -txd switch.)")
                    Console.Error.WriteLine(" -n nn              # of abbreviations to generate (default = 96).")
                    Console.Error.WriteLine(" --onlyrefactor     Skip calculation of abbrevations and only print information about duplicate long strings.")
                    Console.Error.WriteLine(" -r3                Always round to 3 for fast and deep rounding. Normally rounding")
                    Console.Error.WriteLine("                    to 6 is used for strings stored in high memory for z4+ games.")
                    Console.Error.WriteLine(" --txd <file>       Use text extracted from a compiled file with the ZTool, Txd.")
                    Console.Error.WriteLine("                    The file is generated by:")
                    Console.Error.WriteLine("                       txd -ag <game> > <game>.txd")
                    Console.Error.WriteLine("                    (Always used in conjunction with the -infodump switch.)")
                    Console.Error.WriteLine(" -v1 - v8           Z-machine version. 1-3: Round to 3 for high strings")
                    Console.Error.WriteLine("                                       4-7: Round to 6 for high strings")
                    Console.Error.WriteLine("                                         8: Round to 12 for high strings")
                    Console.Error.WriteLine(" -v                 Verbose. Prints extra information.")
                    Console.Error.WriteLine(" path-to-game       Use this path. If omitted the current path is used.")
                    Console.Error.WriteLine()
                    Console.Error.WriteLine("ZAbbrevMaker executed without any switches in folder with zap-files is")
                    Console.Error.WriteLine("the same as 'ZAbbrevMaker -df'.")
                    Exit Sub
                Case "-i"
                    inform6StyleText = True
                Case "-c0"
                    TextEncoding = System.Text.Encoding.ASCII
                Case "-cu"
                    TextEncoding = System.Text.Encoding.UTF8
                Case "-c1"
                    TextEncoding = System.Text.Encoding.Latin1
                Case "-v1", "-v2", "-v3"
                    zVersion = 3            ' Rounding3
                Case "-v4", "-v5", "-v6", "-v7"
                    zVersion = 5            ' Rounding6
                Case "-v8"
                    zVersion = 8            ' Rounding12
                Case "--infodump"
                    infodumpFilename = args(i + 1)
                    i += 1
                Case "--txd"
                    txdFilename = args(i + 1)
                    i += 1
                Case "--onlyrefactor"
                    onlyRefactor = True
                Case Else
                    If IO.Directory.Exists(args(i)) Then
                        gameDirectory = args(i)
                    End If
            End Select
        Next

        ' Console.SetCursorPosition and Console.GetCursorPosition don't work if output is redirected
        If Console.IsOutputRedirected Or Console.IsErrorRedirected Then OutputRedirected = True

        If forceRoundingTo3 Then zVersion = 3

        If zVersion = 0 Then
            zVersion = 3            ' Default to Rounding3
            tryAutoDetectZVersion = True
        End If

        ' Auto-detect Inform
        If Not inform6StyleText And IO.File.Exists(IO.Path.Combine(gameDirectory, "gametext.txt")) Then
            inform6StyleText = True
        End If

        SearchForAbbreviations(gameDirectory,
                               inform6StyleText,
                               fastRounding,
                              deepRounding,
                               fastBeforeDeep,
                               throwBackLowscorers,
                               printDebug)
    End Sub

    'Algorithm, suggested by MTR
    '1.  Calculate abbreviations, score by naive savings
    '2.  Put them in a max-heap.
    '3.  Remove top of heap abbreviation, add To the set of best abbreviations And parse entire corpus.
    '4.  Compute change In savings (Using optimal parse) And declare that to be the new score for the current abbreviation.
    '5.  If the new score is less than the current score for the top-of-heap, remove the current abbreviation from the 
    '    best_abbreviations set And throw it back on the heap.
    '6.  Repeat from step 3 until enough abbreviations are found or the heap is empty.

    ' See:
    ' https://intfiction.org/t/highly-optimized-abbreviations-computed-efficiently/48753
    ' https://intfiction.org/t/playable-version-of-mini-zork-ii/49326
    ' https://gitlab.com/russotto/zilabbrs
    ' https://github.com/hlabrand/retro-scripts

    Private Sub SearchForAbbreviations(gameDirectory As String,
                                       inform6StyleText As Boolean,
                                       fastRounding As Boolean,
                                       deepRounding As Boolean,
                                       fastBeforeDeep As Boolean,
                                       throwBackLowscorers As Boolean,
                                       printDebug As Boolean)
        Try

            '**********************************************************************************************************************
            '***** Part 1: Reading file(s) and storing all strings in a collection                                            *****
            '**********************************************************************************************************************

            ' Define and start stopwatches to measure times and a objekt to read memory consumption
            Dim swTotal As Stopwatch = Stopwatch.StartNew
            Dim swPart As Stopwatch = Stopwatch.StartNew
            Dim proc As Process = Process.GetCurrentProcess

            Console.Error.WriteLine("ZAbbrevMaker 0.10")

            ' Read file(s) inte one large text string and replace space, quote and LF.
            ' Also count frequency of characters for potential custom alphabet
            Dim searchFor34 As Boolean = False
            Dim searchForCR As Boolean = False
            Dim gameTextList As New List(Of GameText)
            Dim totalSavings As Integer = 0
            Dim gameFilename As String = ""
            Dim packedAddress As Boolean = False
            Dim charFreq As New Dictionary(Of Char, Integer)
            Dim totalCharacters As Integer = 0

            Console.Error.WriteLine()
            Console.Error.WriteLine("Processing files In directory: {0}", gameDirectory)
            Console.Error.WriteLine()
            Console.Error.WriteLine("Progress                               Time (s) Mem (MB)")
            Console.Error.WriteLine("--------                               -------- --------")
            Console.Error.Write("Reading file...".PadRight(40))
            If Not IO.Directory.Exists(gameDirectory) Then
                Console.Error.WriteLine("ERROR: Can't find specified directory.")
                Exit Sub
            End If
            Dim useTxd As Boolean = False
            If infodumpFilename <> "" Or txdFilename <> "" Then useTxd = True
            If infodumpFilename <> "" AndAlso Not IO.File.Exists(IO.Path.Combine(gameDirectory, infodumpFilename)) Then
                Console.Error.WriteLine("ERROR: Can't find infodump-file.")
                Exit Sub
            End If
            If txdFilename <> "" AndAlso Not IO.File.Exists(IO.Path.Combine(gameDirectory, txdFilename)) Then
                Console.Error.WriteLine("ERROR: Can't find txd-file.")
                Exit Sub
            End If

            If inform6StyleText And Not useTxd Then
                ' Inform6 text are in "gametext.txt". 
                ' "gametext.txt" is produced by: inform6.exe -r $TRANSCRIPT_FORMAT=1 <gamefile>.inf
                ' Each line is coded
                '   I:info                          not in game file, don't index
                '   G:game text                     high strings, index and packed address
                '   V:veneer text                   high strings, index and packed address
                '   L:lowmem string                 stored in abbreviation area, index?
                '   A:abbreviation                  don't index
                '   D:dict word                     don't index
                '   O:object name                   obj desc, index
                '   S:symbol                        high strings, index and packed address
                '   X:infix                         debug text, don't index
                '   H:game text inline in opcode    text stored inline with opcode, index
                '   W:veneer text inline in opcode  text stored inline with opcode, index
                ' ^ means CR and ~ means ".
                ' Candidate strings that contains a @ should not be considered.
                ' 6.42 will add "I: Compiled Z-machine version 5" to gametext.txt
                If IO.File.Exists(IO.Path.Combine(gameDirectory, "gametext.txt")) Then
                    If TextEncoding Is Nothing Then
                        'Try to autodetect encoding
                        If IsFileUTF8(IO.Path.Combine(gameDirectory, "gametext.txt")) Then
                            TextEncoding = System.Text.Encoding.UTF8
                        Else
                            TextEncoding = System.Text.Encoding.Latin1
                        End If
                    End If

                    Dim reader As New IO.StreamReader(IO.Path.Combine(gameDirectory, "gametext.txt"), TextEncoding)
                    Dim line As String

                    Do
                        line = reader.ReadLine
                        If line IsNot Nothing Then
                            If "GVLOSHW".Contains(line(0)) Then
                                ' Replace ^, ~ and space
                                line = line.Replace("^", LF_REPLACEMENT)
                                line = line.Replace("~", QUOTE_REPLACEMENT)
                                line = line.Replace(" ", SPACE_REPLACEMENT)

                                If "GVS".Contains(line(0)) Then packedAddress = True Else packedAddress = False

                                Dim gameTextLine As New GameText(line.Substring(3)) With {.packedAddress = packedAddress}
                                If line(0) = "O" Then gameTextLine.objectDescription = True
                                gameTextList.Add(gameTextLine)
                                totalCharacters += gameTextLine.TextSB.Length

                                ' Add characters to charFreq
                                For i As Integer = 3 To line.Length - 1
                                    Dim c As Char = line(i)
                                    If Not (c = LF_REPLACEMENT Or c = QUOTE_REPLACEMENT Or c = SPACE_REPLACEMENT Or ASCII(c) = 27) Then
                                        charFreq.TryAdd(c, 0)
                                        charFreq(c) += 1
                                    End If
                                Next
                            Else
                                If line.StartsWith("I: [Compiled Z-machine version") And tryAutoDetectZVersion Then
                                    zVersion = CInt(line(31).ToString)
                                End If
                            End If
                        End If
                    Loop Until line Is Nothing
                    reader.Close()
                Else
                    Console.Error.WriteLine()
                    Console.Error.WriteLine("ERROR: Found no 'gametext.txt' in directory.")
                    Exit Sub
                End If
            End If

            If Not inform6StyleText And Not useTxd Then
                ' Get text from zap-files and store every line in a list of strings.
                ' The ".GSTR", ".STRL", "PRINTI" and "PRINTR" Op-codes contains the text.
                ' Every pattern is stored in a dictionary with the pattern as key.
                For Each fileName As String In IO.Directory.GetFiles(gameDirectory)
                    Dim startPos As Integer = 0

                    If String.Equals(IO.Path.GetExtension(fileName), ".ZAP", StringComparison.OrdinalIgnoreCase) And Not fileName.Contains("_freq", StringComparison.OrdinalIgnoreCase) Then
                        If gameFilename = "" OrElse IO.Path.GetFileName(fileName).Length < gameFilename.Length Then gameFilename = IO.Path.GetFileName(fileName)

                        If TextEncoding Is Nothing Then
                            If IsFileUTF8(fileName) Then
                                TextEncoding = System.Text.Encoding.UTF8
                            Else
                                TextEncoding = System.Text.Encoding.Latin1
                            End If

                        End If

                        Dim byteText() As Byte = IO.File.ReadAllBytes(fileName)

                        For i As Integer = 5 To byteText.Length - 1
                            Dim opCodeString As String = TextEncoding.GetString(byteText, i - 5, 5).ToUpper
                            Dim objectDescription As Boolean = False
                            If opCodeString = ".GSTR" Then  ' High strings
                                searchFor34 = True
                                packedAddress = True
                            End If
                            If opCodeString = ".STRL" Then  ' Object descriptions
                                searchFor34 = True
                                packedAddress = False
                                objectDescription = True
                            End If
                            If opCodeString = "RINTI" Then  ' Prints text inline
                                searchFor34 = True
                                packedAddress = False
                            End If
                            If opCodeString = "RINTR" Then  ' Prints text inline + CRLF + RTRUE
                                searchFor34 = True
                                packedAddress = False
                            End If
                            ' zversion is only relevant if we want to round to 6 zchars for strings in high memory
                            ' ZAPF inserts the file in this order:
                            '   game_freq.zap
                            '   game_data.zap
                            '   game.zap
                            '   game_str.zap
                            '
                            '   dynamic memory : Everything to the label IMPURE (game_data.zap)
                            '   static memory  : Between IMPURE and ENDLOD (game_data.zap)
                            '   high memory    : Everything after ENDLOD
                            '
                            '   Only .GSTR is relevant for rounding to anything other than 3 because text
                            '   in game.zap (inside code) always rounds to 3.
                            If opCodeString = ".NEW " And tryAutoDetectZVersion Then
                                zVersion = byteText(i) - 48
                                If zVersion < 4 Then zVersion = 3                       'Rounding3
                                If zVersion > 3 And zVersion < 8 Then zVersion = 5      'Rounding6, version 8 --> rounding12 
                            End If

                            If searchFor34 And byteText(i) = 34 Then
                                startPos = i
                                searchFor34 = False
                                searchForCR = True
                            End If

                            If searchForCR And byteText(i) = 13 Then
                                searchForCR = False

                                ' Replace ", [LF] & Space with printable and legal characters for a Key
                                If (i - startPos - 2) > 0 Then
                                    Dim byteTemp(i - startPos - 3) As Byte
                                    For j As Integer = 0 To byteTemp.Length - 1
                                        Dim byteChar As Byte = byteText(startPos + 1 + j)
                                        If byteChar = 10 Then byteChar = ASCII(LF_REPLACEMENT)
                                        If byteChar = 32 Then byteChar = ASCII(SPACE_REPLACEMENT)
                                        If byteChar = 34 Then byteChar = ASCII(QUOTE_REPLACEMENT)
                                        byteTemp(j) = byteChar
                                    Next

                                    ' Create dictionary. Replace two double-quotes with one (the first is an escape-char). 
                                    Dim gameTextLine As New GameText(TextEncoding.GetString(byteTemp).Replace(String.Concat(QUOTE_REPLACEMENT, QUOTE_REPLACEMENT), QUOTE_REPLACEMENT)) With {.packedAddress = packedAddress, .objectDescription = True}
                                    gameTextList.Add(gameTextLine)
                                    totalCharacters += gameTextLine.TextSB.Length

                                    ' Add characters to charFreq
                                    For j As Integer = 0 To gameTextLine.text.Length - 1
                                        Dim c As Char = gameTextLine.text(j)
                                        If Not (c = LF_REPLACEMENT Or c = QUOTE_REPLACEMENT Or c = SPACE_REPLACEMENT Or ASCII(c) = 27) Then
                                            charFreq.TryAdd(c, 0)
                                            charFreq(c) += 1
                                        End If
                                    Next

                                End If
                            End If
                        Next
                    End If
                Next
            End If

            If useTxd Then
                ' Get text from output generated by the ZTools, Infodump and TXD.
                ' infodump needs the switch -o and -i:
                '       infodump -io <gamefile> > <gamefile>.infodump
                ' txd need the switch -a to format text in Inform style
                '       txd -ag <gamefile> > <gamefile>.txd
                ' Inform/ZIL and version are determined by header info. If header-info is missing ZIL, version 3 is assumed.
                If IsFileUTF8(IO.Path.Combine(gameDirectory, infodumpFilename)) Then
                    TextEncoding = System.Text.Encoding.UTF8
                Else
                    TextEncoding = System.Text.Encoding.Latin1
                End If

                Dim byteInfodump() As Byte = IO.File.ReadAllBytes(IO.Path.Combine(gameDirectory, infodumpFilename))
                Dim startPos As Integer = 0
                searchFor34 = False
                For i As Integer = 13 To byteInfodump.Length - 1
                    Dim infodumpString As String = TextEncoding.GetString(byteInfodump, i - 13, 13).ToUpper
                    If infodumpString = "DESCRIPTION: " Then searchFor34 = True
                    If infodumpString = "Z-CODE VERSIO" Then zVersion = byteInfodump(i + 13) - 48
                    If infodumpString = "INFORM VERSIO" Then
                        Dim sTemp As String = TextEncoding.GetString(byteInfodump, i + 5, 13).ToUpper.Trim
                        If sTemp <> "ZAPF" Then inform6StyleText = True
                    End If

                    If searchFor34 And byteInfodump(i) = 34 Then
                        startPos = i
                        searchFor34 = False
                        searchForCR = True
                    End If

                    If searchForCR And byteInfodump(i) = 13 Then
                        searchForCR = False

                        ' Replace ", [LF] & Space with printable and legal characters for a Key
                        If (i - startPos - 2) > 0 Then
                            Dim byteTemp(i - startPos - 3) As Byte
                            For j As Integer = 0 To byteTemp.Length - 1
                                Dim byteChar As Byte = byteInfodump(startPos + 1 + j)
                                If byteChar = 10 Or byteChar = 94 Then byteChar = ASCII(LF_REPLACEMENT)
                                If byteChar = 32 Then byteChar = ASCII(SPACE_REPLACEMENT)
                                If byteChar = 34 Then byteChar = ASCII(QUOTE_REPLACEMENT)
                                byteTemp(j) = byteChar
                            Next

                            ' Create dictionary. Replace two double-quotes with one (the first is an escape-char). 
                            Dim gameTextLine As New GameText(TextEncoding.GetString(byteTemp).Replace(String.Concat(QUOTE_REPLACEMENT, QUOTE_REPLACEMENT), QUOTE_REPLACEMENT)) With {.packedAddress = False, .objectDescription = True}
                            gameTextList.Add(gameTextLine)
                            totalCharacters += gameTextLine.TextSB.Length

                            ' Add characters to charFreq
                            For j As Integer = 0 To gameTextLine.text.Length - 1
                                Dim c As Char = gameTextLine.text(j)
                                If Not (c = LF_REPLACEMENT Or c = QUOTE_REPLACEMENT Or c = SPACE_REPLACEMENT Or ASCII(c) = 27) Then
                                    charFreq.TryAdd(c, 0)
                                    charFreq(c) += 1
                                End If
                            Next

                        End If
                    End If
                Next

                If IsFileUTF8(IO.Path.Combine(gameDirectory, txdFilename)) Then
                    TextEncoding = System.Text.Encoding.UTF8
                Else
                    TextEncoding = System.Text.Encoding.Latin1
                End If

                Dim byteTxd() As Byte = IO.File.ReadAllBytes(IO.Path.Combine(gameDirectory, txdFilename))
                startPos = 0
                searchFor34 = False
                Dim codeArea As Boolean = True
                packedAddress = False
                For i As Integer = 9 To byteTxd.Length - 1
                    Dim txdString As String = TextEncoding.GetString(byteTxd, i - 9, 9).ToUpper
                    If codeArea And txdString = "PRINT    " Then searchFor34 = True
                    If codeArea And txdString = "PRINT_RET" Then searchFor34 = True
                    If txdString = "D OF CODE" Then codeArea = False : searchFor34 = True : packedAddress = True

                    If searchFor34 And byteTxd(i) = 34 Then
                        startPos = i
                        searchFor34 = False
                        searchForCR = True
                        i += 1
                    End If

                    If searchForCR And byteTxd(i) = 34 Then
                        searchForCR = False
                        If Not codeArea Then searchFor34 = True

                        ' Replace ", [LF] & Space with printable and legal characters for a Key
                        If (i - startPos - 1) > 0 Then
                            Dim byteTemp(i - startPos - 2) As Byte
                            For j As Integer = 0 To byteTemp.Length - 1
                                Dim byteChar As Byte = byteTxd(startPos + 1 + j)
                                If byteChar = 13 Then byteChar = ASCII(CChar("}"))      ' Supress CR
                                If byteChar = 10 Then byteChar = 32                     ' Convert LF to SPACE
                                If byteChar = 94 Then byteChar = ASCII(LF_REPLACEMENT)
                                If byteChar = 32 Then byteChar = ASCII(SPACE_REPLACEMENT)
                                If byteChar = 34 Then byteChar = ASCII(QUOTE_REPLACEMENT)
                                byteTemp(j) = byteChar
                            Next

                            ' Create dictionary. Replace two double-quotes with one (the first is an escape-char). 
                            Dim gameTextLine As New GameText(TextEncoding.GetString(byteTemp).Replace(String.Concat(QUOTE_REPLACEMENT, QUOTE_REPLACEMENT), QUOTE_REPLACEMENT)) With {.packedAddress = packedAddress}
                            gameTextLine.text = gameTextLine.text.Replace("}", "")
                            gameTextList.Add(gameTextLine)
                            totalCharacters += gameTextLine.TextSB.Length

                            ' Add characters to charFreq
                            For j As Integer = 0 To gameTextLine.text.Length - 1
                                Dim c As Char = gameTextLine.text(j)
                                If Not (c = LF_REPLACEMENT Or c = QUOTE_REPLACEMENT Or c = SPACE_REPLACEMENT Or ASCII(c) = 27) Then
                                    charFreq.TryAdd(c, 0)
                                    charFreq(c) += 1
                                End If
                            Next

                        End If
                    End If
                Next

            End If
            proc.Refresh()
            swPart.Stop()
            Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} characters, {3}", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), totalCharacters, String.Concat(TextEncoding.BodyName, ", ", TextEncoding.EncodingName))

            '**********************************************************************************************************************
            '***** Part 2: Fix alphabet and build a suffix array over all strings                                             *****
            '**********************************************************************************************************************

            swPart = Stopwatch.StartNew
            Console.Error.Write("Building suffix arrays...".PadRight(40))

            If customAlphabet Then
                Dim charFreqList As List(Of KeyValuePair(Of Char, Integer)) =
                                                    (From tPair As KeyValuePair(Of Char, Integer) _
                                                     In charFreq Order By tPair.Value Descending
                                                     Select tPair).ToList

                ' Caclculate cost with default alphabet
                For Each c As Char In alphabet0
                    alphabet0Hash.Add(c)
                Next
                alphabet0Hash.Add(SPACE_REPLACEMENT)
                For Each c As Char In alphabet1
                    alphabet1And2Hash.Add(c)
                Next
                For Each c As Char In alphabet2
                    alphabet1And2Hash.Add(c)
                Next
                alphabet1And2Hash.Add(QUOTE_REPLACEMENT)
                alphabet1And2Hash.Add(LF_REPLACEMENT)
                For Each gameTextLine As GameText In gameTextList
                    gameTextLine.costWithDefaultAlphabet = ZstringCost(gameTextLine.text)
                Next
                alphabet0Hash.Clear()
                alphabet1And2Hash.Clear()

                Dim alphabet As String = ""
                For i As Integer = 0 To 74
                    alphabet = String.Concat(alphabet, charFreqList(i).Key)
                Next
                alphabet0 = SortAlphabet(alphabet.Substring(0, 26), defaultA0)
                alphabet1 = SortAlphabet(alphabet.Substring(26, 49), String.Concat(defaultA1, defaultA2))
                alphabet2 = alphabet1.Substring(26)
                alphabet1 = alphabet1.Substring(0, 26)
                If printDebug Then
                    Console.Error.WriteLine()
                    Console.Error.WriteLine()
                    Console.Error.WriteLine(String.Concat("Alphabet = ", Chr(34), alphabet, Chr(34)))
                    Console.Error.WriteLine()
                    Console.Error.Write(Space(40))
                End If
            End If

            ' Store alphabet in hashsets (slightly faster) and add SPACE_REPLACEMENT to A0 and
            ' other replacements to A2 because zcharcost becomes more optimized without OrElse
            For Each c As Char In alphabet0
                alphabet0Hash.Add(c)
            Next
            alphabet0Hash.Add(SPACE_REPLACEMENT)
            For Each c As Char In alphabet1
                alphabet1And2Hash.Add(c)
            Next
            For Each c As Char In alphabet2
                alphabet1And2Hash.Add(c)
            Next
            alphabet1And2Hash.Add(QUOTE_REPLACEMENT)
            alphabet1And2Hash.Add(LF_REPLACEMENT)
            If customAlphabet Then
                For Each gameTextLine As GameText In gameTextList
                    gameTextLine.costWithCustomAlphabet = ZstringCost(gameTextLine.text)
                Next
            End If

            Dim pattern As PatternData = Nothing

            'Build a suffix array
            Dim texts As New List(Of String)
            Dim patternDictionary As New Dictionary(Of String, PatternData)     ' Use a dictionary to filter out duplicates of patterns
            For i As Integer = 0 To gameTextList.Count - 1
                texts.Add(gameTextList(i).text)
                gameTextList(i).suffixArray = SuffixArray.BuildSuffixArray(gameTextList(i).text)
                gameTextList(i).lcpArray = SuffixArray.BuildLCPArray(gameTextList(i).text, gameTextList(i).suffixArray)
            Next
            Dim gsaString As String = SuffixArray.BuildGeneralizedSuffixArrayString(texts)
            Dim sa() As Integer = SuffixArray.BuildSuffixArray(gsaString)
            Dim lcp() As Integer = SuffixArray.BuildLCPArray(gsaString, sa)
            proc.Refresh()
            swPart.Stop()
            Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} potential patterns", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), SuffixArray.CountUniquePatterns(lcp))

            '**********************************************************************************************************************
            '***** Part 3: Extract all unique patterns from strings using suffix array and store in a dictionary              *****
            '*****         Calculates cost and frequency of all patterns.                                                     *****
            '**********************************************************************************************************************

            swPart = Stopwatch.StartNew
            Console.Error.Write("Extracting viable patterns...".PadRight(40))
            For i As Integer = SuffixArray.Count(lcp, 0, 1) To lcp.Length - 2  ' The iteration kan skip all suffixes that start with the seperator 
                If lcp(i + 1) > 0 Then                                         ' patterns with lcp=0 have a frequency of 1 and can be discarded
                    Dim start As Integer = 1
                    If i > 0 Then start = lcp(i)
                    If start < 1 Then start = 1
                    For j As Integer = start To lcp(i + 1)
                        Dim sKey As String = gsaString.Substring(sa(i), j)
                        If Not sKey.Contains(ControlChars.VerticalTab) And Not sKey.Contains(CChar("@")) Then
                            Dim cost As Integer = ZstringCost(sKey)
                            Dim freq As Integer = SuffixArray.Count(lcp, i, sKey.Length)
                            If freq > 1 And (freq * (cost - 2)) - ((cost + 2) \ 3) * 3 > 0 Then   ' Same formula as in PatternData.Score
                                If Not patternDictionary.ContainsKey(sKey) Then
                                    ' New potential pattern, add it to dictionary
                                    patternDictionary(sKey) = New PatternData With {.Cost = cost,
                                                                                    .Frequency = freq,
                                                                                    .Key = sKey}
                                End If
                            End If
                        End If
                    Next
                End If
            Next
            If gameTextList.Count = 0 Then
                Console.Error.WriteLine("ERROR: No data to index.")
                Exit Sub
            End If
            swPart.Stop()
            proc.Refresh()
            Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} strings, {3:##,#} patterns extracted", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), gameTextList.Count, patternDictionary.Count)

            '**********************************************************************************************************************
            '***** Part 4: Put all patterns up to 20 characters on a max heap. For patterns longer than 20 characters only    *****
            '*****         the patterns that don't contains a subpattern. The max heap have the one with highest potential    *****
            '*****         savings are on top.                                                                                *****
            '**********************************************************************************************************************

            ' Add to a Max Heap
            swPart = Stopwatch.StartNew
            Console.Error.Write("Build max heap with naive score...".PadRight(40))
            Dim maxHeap As New PriorityQueue(Of PatternData, Integer)(New PatternComparer)
            Dim maxHeapRefactor As New PriorityQueue(Of PatternData, Integer)(New PatternComparer)
            Dim maxHeapLength As New PriorityQueue(Of PatternData, Integer)(New PatternComparer)
            For Each phrase As KeyValuePair(Of String, PatternData) In patternDictionary
                phrase.Value.Savings = phrase.Value.Score
                If phrase.Value.Savings > 0 Then
                    If phrase.Key.Length <= CUTOFF_LONG_PATTERN Then
                        ' Save all short patterns
                        maxHeap.Enqueue(phrase.Value, phrase.Value.Savings)
                    Else
                        ' Store longer patterns for later  
                        maxHeapLength.Enqueue(phrase.Value, phrase.Key.Length)
                    End If
                End If
            Next
            ' Only save the longest pattern on not the substrings that are contained inside them
            Dim tempHashSet As New HashSet(Of String)
            While maxHeapLength.Count > 0
                Dim candidate As PatternData = maxHeapLength.Dequeue
                tempHashSet.Add(candidate.Key.Substring(1))
                tempHashSet.Add(candidate.Key.Substring(0, candidate.Key.Length - 1))
                If Not tempHashSet.Contains(candidate.Key) Then
                    maxHeap.Enqueue(candidate, candidate.Savings)
                    maxHeapRefactor.Enqueue(candidate, candidate.Key.Length)
                End If
            End While
            tempHashSet = Nothing
            maxHeapLength = Nothing
            swPart.Stop()
            proc.Refresh()
            Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  {2:##,#} patterns added to heap", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), maxHeap.Count)

            '**********************************************************************************************************************
            '***** Part 5: Pick abbreviations from heap and rescore them with Wagner's method for optimal parse.              *****
            '**********************************************************************************************************************


            ' Optimal Parse
            Dim bestCandidateList As New List(Of PatternData)
            Dim currentAbbrev As Integer = 0
            Dim previousSavings As Integer = 0
            Dim oversample As Integer = 0
            Dim latestTotalBytes As Integer = 0

            ' Init the total rounding penalty without abbreviations
            totalSavings = 0
            If throwBackLowscorers Then oversample = 5
            If Not onlyRefactor Then
                swPart = Stopwatch.StartNew
                Console.Error.Write("Rescoring with optimal parse...".PadRight(40))
                If printDebug Then
                    Console.Error.WriteLine()
                End If
                If Not OutputRedirected And Not printDebug Then
                    Console.SetCursorPosition(35, Console.GetCursorPosition.Top)
                    Console.Write("{0,3}%", 0)
                End If
                If printDebug Then Console.Error.WriteLine()

                Do
                    Dim candidate As PatternData = maxHeap.Dequeue
                    bestCandidateList.Add(candidate)
                    Dim currentSavings As Integer = RescoreOptimalParse(gameTextList, bestCandidateList, False, zVersion)
                    Dim deltaSavings As Integer = currentSavings - previousSavings
                    If deltaSavings < maxHeap.Peek.Savings Then
                        ' If delta savings is less than top of heap then remove current abbrev and reinsert it in heap with new score and try next from heap
                        Dim KPD As PatternData = bestCandidateList(currentAbbrev)
                        KPD.Savings = currentSavings - previousSavings
                        bestCandidateList.RemoveAt(currentAbbrev)
                        maxHeap.Enqueue(KPD, KPD.Savings)
                    Else
                        If printDebug Then Console.Error.WriteLine("Adding abbrev no " & (currentAbbrev + 1).ToString & ": " & FormatAbbreviation(bestCandidateList(currentAbbrev).Key) & ", Total savings: " & currentSavings.ToString)
                        Dim latestSavings As Integer = currentSavings - previousSavings
                        currentAbbrev += 1
                        previousSavings = currentSavings
                        totalSavings = currentSavings
                        If throwBackLowscorers Then
                            ' put everthing back on heap that has lower savings than latest added
                            Dim bNeedRecalculation As Boolean = False
                            For i As Integer = bestCandidateList.Count - 1 To 0 Step -1
                                If bestCandidateList(i).Savings < latestSavings Then
                                    If printDebug Then Console.Error.WriteLine("Removing abbrev: " & FormatAbbreviation(bestCandidateList(i).Key))
                                    maxHeap.Enqueue(bestCandidateList(i), bestCandidateList(i).Savings)
                                    bestCandidateList.RemoveAt(i)
                                    i -= 1
                                    currentAbbrev -= 1
                                    bNeedRecalculation = True
                                End If
                            Next
                            If bNeedRecalculation Then
                                previousSavings = RescoreOptimalParse(gameTextList, bestCandidateList, False, zVersion)
                                If printDebug Then Console.Error.WriteLine("Total savings: " & previousSavings.ToString & " - Total Abbrevs: " & currentAbbrev.ToString)
                            End If
                        End If
                    End If

                    Dim progress As Integer = CInt(currentAbbrev * 100 / (NumberOfAbbrevs + oversample))
                    If Not OutputRedirected And Not printDebug And progress Mod 5 = 0 Then
                        Console.SetCursorPosition(35, Console.GetCursorPosition.Top)
                        Console.Write("{0,3}%", progress)
                    End If

                Loop Until currentAbbrev = (NumberOfAbbrevs + oversample) Or maxHeap.Count = 0
                latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                If printDebug Then
                    Console.Error.WriteLine()
                    Console.Error.Write(Space(40))
                End If
                swPart.Stop()
                proc.Refresh()
                If Not OutputRedirected And Not printDebug Then
                    Console.SetCursorPosition(35, Console.GetCursorPosition.Top)
                    Console.Write("{0,3}% ", 100)
                End If
                Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  Total saving {2:##,#} z-chars, text = {3:##,#} bytes", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), totalSavings, latestTotalBytes)

                If printDebug Then
                    Console.Error.WriteLine()
                    If inform6StyleText Then
                        PrintAbbreviationsI6(AbbrevSort(bestCandidateList, False), True)
                    Else
                        PrintAbbreviations(AbbrevSort(bestCandidateList, False), gameFilename, True)
                    End If
                    Console.Error.WriteLine()
                End If

                ' Restore best candidate list to numberOfAbbrevs patterns
                For i As Integer = (NumberOfAbbrevs + oversample - 1) To NumberOfAbbrevs Step -1
                    maxHeap.Enqueue(bestCandidateList(i), bestCandidateList(i).Savings)
                    bestCandidateList.RemoveAt(i)
                Next
            End If

            '**********************************************************************************************************************
            '***** Part 6: Pass 2 & 3. Try potential abbreviations to see if they save bytes by minimizing the space lost     *****
            '*****         to padding.                                                                                        *****
            '**********************************************************************************************************************

            If Not onlyRefactor Then
                For pass As Integer = 0 To 1
                    Dim prevTotSavings As Integer = 0
                    totalSavings = 0
                    If (pass = 0 And deepRounding And Not fastBeforeDeep) Or (pass = 1 And deepRounding And fastBeforeDeep) Then
                        ' Ok, we now have numberOfAbbrevs abbreviations
                        ' Recalculate savings taking rounding into account and test a number of candidates to see if they yield a better result.
                        ' This can't be done exactly because strings that are inline the z-code on z4+ have the rounding cost for packed addresses
                        ' shared between potentially multiple string inside the same code block and the code-block itself. Sometimes the saving
                        ' can be better if ignoring rounding > 3 and force it to 3 with (-r3).
                        swPart = Stopwatch.StartNew
                        Console.Error.Write("Refining picked abbreviations... ".PadRight(40))
                        If printDebug Then
                            Console.Error.WriteLine()
                        End If
                        If Not OutputRedirected And Not printDebug Then
                            Console.SetCursorPosition(35, Console.GetCursorPosition.Top)
                            Console.Write("{0,3}%", 0)
                        End If
                        If printDebug Then Console.Error.WriteLine()
                        Dim passes As Integer = 0
                        Dim previousTotalBytes As Integer = latestTotalBytes
                        Dim maxAbbreviationLength As Integer = 0
                        For i As Integer = 0 To bestCandidateList.Count - 1
                            If bestCandidateList(i).Key.Length > maxAbbreviationLength And bestCandidateList(i).Key.Length <= CUTOFF_LONG_PATTERN Then
                                maxAbbreviationLength = bestCandidateList(i).Key.Length
                            End If
                        Next
                        maxAbbreviationLength += 2
                        Do While passes < NUMBER_OF_PASSES And maxHeap.Count > 0
                            Dim runnerup As PatternData = maxHeap.Dequeue
                            If runnerup.Key.Length > maxAbbreviationLength Then Continue Do
                            passes += 1
                            If Not OutputRedirected And Not printDebug And passes Mod (NUMBER_OF_PASSES / 20) = 0 Then
                                Console.SetCursorPosition(35, Console.GetCursorPosition.Top)
                                Console.Write("{0,3}%", CInt(passes / (NUMBER_OF_PASSES / 100)))
                            End If
                            Dim replaced As Boolean = False
                            'For i = bestCandidateList.Count - 1 To 0 Step -1    ' Search from lowest savings uppward
                            For i = 0 To bestCandidateList.Count - 1            ' Try replacing highest freq first
                                If Not replaced Then
                                    If runnerup.Key.StartsWith(bestCandidateList(i).Key) Or
                                      runnerup.Key.EndsWith(bestCandidateList(i).Key) Or
                                      bestCandidateList(i).Key.StartsWith(runnerup.Key) Or
                                      bestCandidateList(i).Key.EndsWith(runnerup.Key) Or
                                      runnerup.Key.Contains(bestCandidateList(i).Key) Or
                                      bestCandidateList(i).Key.Contains(runnerup.Key) Then
                                        Dim tempCandidate As PatternData = bestCandidateList(i)
                                        bestCandidateList.Insert(i, runnerup)
                                        bestCandidateList.RemoveAt(i + 1)
                                        latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                                        Dim deltaSavings As Integer = previousTotalBytes - latestTotalBytes
                                        If deltaSavings > 0 Then
                                            previousTotalBytes = latestTotalBytes
                                            replaced = True
                                            If printDebug Then Console.Error.WriteLine("Replacing " & FormatAbbreviation(tempCandidate.Key) & " with " & FormatAbbreviation(runnerup.Key) & ", saving " & deltaSavings.ToString & " bytes, pass = " & passes.ToString)
                                        Else
                                            bestCandidateList.Insert(i, tempCandidate)
                                            bestCandidateList.RemoveAt(i + 1)
                                        End If
                                    End If
                                End If

                            Next
                        Loop
                        totalSavings = RescoreOptimalParse(gameTextList, bestCandidateList, False, zVersion)
                        swPart.Stop()
                        proc.Refresh()
                        If Not OutputRedirected And Not printDebug Then
                            Console.SetCursorPosition(35, Console.GetCursorPosition.Top)
                            Console.Write("100% ")
                        End If
                        If printDebug Then
                            Console.Error.WriteLine()
                            Console.Error.Write(Space(40))
                        End If
                        Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  Total saving {2:##,#} z-chars, text = {3:##,#} bytes", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), totalSavings, latestTotalBytes)

                        If pass = 0 And printDebug Then
                            Console.Error.WriteLine()
                            If inform6StyleText Then
                                PrintAbbreviationsI6(AbbrevSort(bestCandidateList, False), True)
                            Else
                                PrintAbbreviations(AbbrevSort(bestCandidateList, False), gameFilename, True)
                            End If
                            Console.Error.WriteLine()
                        End If
                    End If

                    If (pass = 1 And fastRounding And Not fastBeforeDeep) Or (pass = 0 And fastRounding And fastBeforeDeep) Then
                        ' Test if we add/remove initial/trailing space
                        swPart = Stopwatch.StartNew
                        Console.Error.Write("Add/remove initial/trailing space...".PadRight(40))
                        If printDebug Then
                            Console.Error.WriteLine()
                            Console.Error.WriteLine()
                        End If
                        Dim previousTotalBytes As Integer = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                        For i As Integer = 0 To bestCandidateList.Count - 1
                            If bestCandidateList(i).Key.StartsWith(SPACE_REPLACEMENT) Then
                                bestCandidateList(i).Key = bestCandidateList(i).Key.Substring(1)
                                bestCandidateList(i).Cost -= 1
                                bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                                Dim deltaSavings As Integer = previousTotalBytes - latestTotalBytes
                                If deltaSavings > 0 Then
                                    ' Keep it
                                    previousTotalBytes = latestTotalBytes
                                    If printDebug Then Console.Error.WriteLine("Replacing " & FormatAbbreviation(SPACE_REPLACEMENT & bestCandidateList(i).Key) & " with " & FormatAbbreviation(bestCandidateList(i).Key) & ", saving " & deltaSavings.ToString & " bytes")
                                Else
                                    ' Restore
                                    bestCandidateList(i).Key = SPACE_REPLACEMENT & bestCandidateList(i).Key
                                    bestCandidateList(i).Cost += 1
                                    bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                End If
                            Else
                                bestCandidateList(i).Key = SPACE_REPLACEMENT & bestCandidateList(i).Key
                                bestCandidateList(i).Cost += 1
                                bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                                Dim deltaSavings As Integer = previousTotalBytes - latestTotalBytes
                                If deltaSavings > 0 Then
                                    ' Keep it
                                    previousTotalBytes = latestTotalBytes
                                    If printDebug Then Console.Error.WriteLine("Replacing " & FormatAbbreviation(bestCandidateList(i).Key.Substring(1)) & " with " & FormatAbbreviation(bestCandidateList(i).Key) & ", saving " & deltaSavings.ToString & " bytes")
                                Else
                                    ' Restore
                                    bestCandidateList(i).Key = bestCandidateList(i).Key.Substring(1)
                                    bestCandidateList(i).Cost -= 1
                                    bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                End If
                            End If
                        Next

                        For i As Integer = 0 To bestCandidateList.Count - 1
                            If bestCandidateList(i).Key.EndsWith(SPACE_REPLACEMENT) Then
                                bestCandidateList(i).Key = bestCandidateList(i).Key.Substring(0, bestCandidateList(i).Key.Length - 1)
                                bestCandidateList(i).Cost -= 1
                                bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                                Dim deltaSavings As Integer = previousTotalBytes - latestTotalBytes
                                If deltaSavings > 0 Then
                                    ' Keep it
                                    previousTotalBytes = latestTotalBytes
                                    If printDebug Then Console.Error.WriteLine("Replacing " & FormatAbbreviation(bestCandidateList(i).Key & SPACE_REPLACEMENT) & " with " & FormatAbbreviation(bestCandidateList(i).Key) & ", saving " & deltaSavings.ToString & " bytes")
                                Else
                                    ' Restore
                                    bestCandidateList(i).Key = bestCandidateList(i).Key & SPACE_REPLACEMENT
                                    bestCandidateList(i).Cost += 1
                                    bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                End If
                            Else
                                bestCandidateList(i).Key = bestCandidateList(i).Key & SPACE_REPLACEMENT
                                bestCandidateList(i).Cost += 1
                                bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                latestTotalBytes = RescoreOptimalParse(gameTextList, bestCandidateList, True, zVersion)
                                Dim deltaSavings As Integer = previousTotalBytes - latestTotalBytes
                                If deltaSavings > 0 Then
                                    ' Keep it
                                    previousTotalBytes = latestTotalBytes
                                    If printDebug Then Console.Error.WriteLine("Replacing " & FormatAbbreviation(bestCandidateList(i).Key.Substring(0, bestCandidateList(i).Key.Length - 1)) & " with " & FormatAbbreviation(bestCandidateList(i).Key) & ", saving " & deltaSavings.ToString & " bytes")
                                Else
                                    ' Restore
                                    bestCandidateList(i).Key = bestCandidateList(i).Key.Substring(0, bestCandidateList(i).Key.Length - 1)
                                    bestCandidateList(i).Cost -= 1
                                    bestCandidateList(i).UpdateOccurrences(gameTextList, True)
                                End If
                            End If
                        Next
                        totalSavings = RescoreOptimalParse(gameTextList, bestCandidateList, False, zVersion)
                        swPart.Stop()
                        proc.Refresh()
                        If printDebug Then
                            Console.Error.WriteLine()
                            Console.Error.Write(Space(40))
                        End If
                        Console.Error.WriteLine("{0,7:0.000} {1,8:0.00}  Total saving {2:##,#} z-chars, text = {3:##,#} bytes", swPart.ElapsedMilliseconds / 1000, proc.PrivateMemorySize64 / (1024 * 1024), totalSavings, latestTotalBytes)

                        If printDebug Then
                            Console.Error.WriteLine()
                            If inform6StyleText Then
                                PrintAbbreviationsI6(AbbrevSort(bestCandidateList, False), True)
                            Else
                                PrintAbbreviations(AbbrevSort(bestCandidateList, False), gameFilename, True)
                            End If
                            If customAlphabet Then Console.Error.WriteLine()
                        End If
                    End If
                Next
            End If

            '**********************************************************************************************************************
            '***** Part 7: Finishing up and printing the result                                                               *****
            '**********************************************************************************************************************

            Dim totalSavingsAlphabet As Integer = 0
            If Not onlyRefactor Then
                If customAlphabet Then
                    Dim costDefaultAlphabet As Integer = 0
                    Dim costCustomAlphabet As Integer = 0

                    For Each gameTextLine As GameText In gameTextList
                        costDefaultAlphabet += gameTextLine.costWithDefaultAlphabet
                        costCustomAlphabet += gameTextLine.costWithCustomAlphabet
                    Next
                    totalSavingsAlphabet = costDefaultAlphabet - costCustomAlphabet
                    totalSavings += totalSavingsAlphabet
                    Console.Error.Write("Applying custom alphabet...".PadRight(58))
                    Console.Error.WriteLine("Total saving {0:##,#} z-chars", totalSavings)
                End If
            End If

            swTotal.Stop()
            proc.Refresh()
            Console.Error.WriteLine()
            Console.Error.WriteLine("Total elapsed time: {0,7:0.000} s", swTotal.ElapsedMilliseconds / 1000)
            Console.Error.WriteLine()

            If Not onlyRefactor Then
                RescoreOptimalParse(gameTextList, bestCandidateList, False, zVersion)
                totalSavings = 0
                Dim maxAbbrevs As Integer = bestCandidateList.Count - 1
                If maxAbbrevs >= NumberOfAbbrevs Then maxAbbrevs = NumberOfAbbrevs - 1
                For i As Integer = 0 To maxAbbrevs
                    totalSavings += bestCandidateList(i).Savings
                Next
                If customAlphabet Then
                    Console.Error.WriteLine(String.Concat("Custom alphabet would save ", totalSavingsAlphabet.ToString("##,#"), " z-chars total (~", CInt(totalSavingsAlphabet * 2 / 3).ToString("##,#"), " bytes)"))
                End If
                Console.Error.WriteLine(String.Concat("Abbreviations would save ", totalSavings.ToString("##,#"), " z-chars total (~", CInt(totalSavings * 2 / 3).ToString("##,#"), " bytes)"))
                Console.Error.WriteLine()
            End If

            Dim totalBytes As Integer = 0
            Dim totalWasted As Integer = 0

            If Not onlyRefactor Then
                For pass As Integer = 0 To 1
                    Dim wasted(11) As Integer
                    For Each line As GameText In gameTextList
                        If pass = 0 And line.packedAddress Then wasted(line.latestRoundingCost) += 1
                        If pass = 1 And Not line.packedAddress Then wasted(line.latestRoundingCost) += 1
                    Next
                    If pass = 0 Then Console.Error.WriteLine("High memory strings ({0:##,#} strings):", wasted.Sum)
                    If pass = 1 Then Console.Error.WriteLine("Dynamic and static memory strings ({0:##,#} strings):", wasted.Sum)
                    For i = 11 To 0 Step -1
                        Dim bytes As Integer = wasted(i)
                        If i = 0 Then bytes = 0
                        If i > 3 Then bytes *= 2
                        If i > 7 Then bytes *= 2
                        totalBytes += bytes
                        totalWasted += wasted(i) * i
                        If wasted(i) > 0 Then Console.Error.WriteLine("{0,6:##,#} strings with {1,2} empty z-chars, total = {2,7:##,0}, {3,6:##,0} bytes", wasted(i), i, wasted(i) * i, bytes)
                    Next
                Next
                Console.Error.WriteLine("Total:                                      {0,9:##,#}, {1,6:##,0} bytes", totalWasted, totalBytes)
                Console.Error.WriteLine()
            End If

            If verbose Or onlyRefactor Then
                If Not onlyRefactor Then
                    ' High memory strings
                    Console.Error.WriteLine("High memory strings (abbreviations inside {}, ^ = linebreak and ~ = double-quote):")
                    For wastedZChars As Integer = 11 To 0 Step -1
                        For i = 0 To gameTextList.Count - 1
                            If gameTextList(i).packedAddress And gameTextList(i).latestRoundingCost = wastedZChars Then
                                Console.Error.WriteLine(gameTextList(i).FinishedText(bestCandidateList))
                            End If
                        Next
                    Next
                    Console.Error.WriteLine()
                    ' Dynamic and static memory strings
                    Console.Error.WriteLine("Dynamic and static memory strings:")
                    For wastedZChars As Integer = 2 To 0 Step -1
                        For i = 0 To gameTextList.Count - 1
                            If Not gameTextList(i).packedAddress And gameTextList(i).latestRoundingCost = wastedZChars Then
                                Console.Error.WriteLine(gameTextList(i).FinishedText(bestCandidateList))
                            End If
                        Next
                    Next
                    Console.Error.WriteLine()
                End If

                ' Refactoring tips
                If maxHeapRefactor.Count > 0 Then
                        Dim totalSavingBytes As Integer = 0
                        Dim objectDescCount As Integer = 0
                        Console.Error.WriteLine("Long repeated strings:")
                        While maxHeapRefactor.Count > 0
                            Dim text As PatternData = maxHeapRefactor.Dequeue
                            text.UpdateOccurrences(gameTextList, False)
                            Dim positionInside As Integer = 0           ' Bit 0=undefined, 1=Equal, 2=starting, 4=ending, 8=inside, 16=includes obj desc
                            For i As Integer = 0 To gameTextList.Count - 1
                                'If gameTextList(i).objectDescription Then
                                '    objectDescCount += 1
                                'Else
                                Dim gametext As String = gameTextList(i).text
                                If text.Occurrences(i) IsNot Nothing Then
                                    If gametext = text.Key Then
                                        positionInside = (positionInside Or 1)
                                    ElseIf gametext.StartsWith(text.Key) Then
                                        positionInside = (positionInside Or 2)
                                    ElseIf gametext.EndsWith(text.Key) Then
                                        positionInside = (positionInside Or 4)
                                    ElseIf gametext.Contains(text.Key) Then
                                        positionInside = (positionInside Or 8)
                                    End If
                                    If gameTextList(i).objectDescription Then positionInside = (positionInside Or 16)
                                End If
                                'End If
                            Next
                            Dim posTxt As String = "(mixed )"
                            If positionInside = 1 Then posTxt = "( full )"
                            If positionInside = 2 Then posTxt = "(start )"
                            If positionInside = 4 Then posTxt = "( end  )"
                            If positionInside = 8 Then posTxt = "(inside)"
                            If (positionInside And 16) = 16 Then posTxt = "(object)"
                            Dim cost As Integer = ZstringCost(text.Key)

                            ' Saving (in bytes) are a bit tricky to calculate.
                            ' PRINT/print_paddr or PRINTB/print_addr cost 2 bytes when printing from a global variable
                            ' and 3 bytes when printing from a direct address in high memory. There's also an extra cost
                            ' for space lost to padding when you split up a string to two or three strings (replacing string
                            ' inside another string). If one is lucky the padding is zero but it's hard to predict because
                            ' new abbreviations are needed afterward. On average splitting a string to two strings will cost
                            ' a byte in z1-z3, two bytes in z4-z7 and four bytes in z8. Splitting to three strings double
                            ' the padding cost.
                            ' In short: this is an estimate based on the string being stored as a constant in high memory
                            ' addressed by a direct address (packed or unpacked).
                            Dim paddingCost As Integer = 2          ' (mixed), (inside)
                            Dim splitCost As Integer = 6            ' (mixed), (inside), assuming direct address, not global
                            If positionInside = 1 Then              ' (full)
                                paddingCost = 0
                                splitCost = 0
                            ElseIf positionInside = 2 Or
                               positionInside = 4 Or
                               positionInside = 6 Then          ' (start), (end)
                                paddingCost = 1
                                splitCost = 3                       ' assuming direct address, not global
                            End If
                            If zVersion > 3 Then paddingCost *= 2
                            If zVersion > 7 Then paddingCost *= 2
                            Dim savingInBytes As Integer = CInt(Math.Ceiling(((text.Frequency - 1 - objectDescCount) * cost) * 2 / 3)) -
                                                       splitCost * (text.Frequency - 1 - objectDescCount) - paddingCost
                            If savingInBytes > 0 Then
                                Console.Error.WriteLine("{0,3}x{1,3} z-chars (~ {2,3} bytes), {3} {4}{5}{6}", text.Frequency - objectDescCount, cost, savingInBytes, posTxt, Chr(34), text.Key.Replace(SPACE_REPLACEMENT, " ").Replace(LF_REPLACEMENT, "^"), Chr(34))
                                totalSavingBytes += savingInBytes
                            End If
                        End While
                        'Console.Error.WriteLine("Total potential saving: {0,6:##,0} bytes", totalSavingBytes)
                        Console.Error.WriteLine()
                    End If
                End If

                If Not onlyRefactor Then
                ' Print result
                If customAlphabet Then
                    If inform6StyleText Then PrintAlphabetI6() Else PrintAlphabet()
                End If
                If inform6StyleText Then
                    PrintAbbreviationsI6(AbbrevSort(bestCandidateList, False), False)
                Else
                    PrintAbbreviations(AbbrevSort(bestCandidateList, False), gameFilename, False)
                End If
            End If
        Catch ex As Exception
            Console.Error.WriteLine("ERROR: ZAbbrevMaker failed.")
            Console.Error.WriteLine(ex.Message)
        End Try
    End Sub

    Public Class PatternComparer
        Implements IComparer(Of Integer)

        Public Function Compare(x As Integer, y As Integer) As Integer Implements IComparer(Of Integer).Compare
            ' Here we compare this instance with other.
            ' If this is supposed to come before other once sorted then
            ' we should return a negative number.
            ' If they are the same, then return 0.
            ' If this one should come after other then return a positive number.
            If x > y Then Return -1
            If x < y Then Return 1
            Return 0
        End Function
    End Class

    Public Class GameText
        Public costWithDefaultAlphabet As Integer = 0
        Public costWithCustomAlphabet As Integer = 0
        Public latestMinimalCost As Integer = 0
        Public latestRoundingCost As Integer = 0
        Public latestPickedAbbreviations() As Integer
        Public suffixArray() As Integer
        Public lcpArray() As Integer
        Public packedAddress As Boolean = False
        Public objectDescription As Boolean = False

        Public Sub New(value As String)
            Me.text = value
        End Sub

        Public text As String = ""
        Private _textSB As Text.StringBuilder
        Public ReadOnly Property TextSB As Text.StringBuilder
            Get
                If _textSB Is Nothing Then
                    _textSB = New Text.StringBuilder(Me.text)
                End If
                Return _textSB
            End Get
        End Property

        Public Function FinishedText(abbreviations As List(Of PatternData)) As String
            Dim returnText As String = Me.text
            For i As Integer = returnText.Length - 1 To 0 Step -1
                If latestPickedAbbreviations(i) > -1 Then
                    Dim abbreviation As String = abbreviations(latestPickedAbbreviations(i)).Key
                    returnText = returnText.Substring(0, i) &
                                 "{" & abbreviation & "}" &
                                 returnText.Substring(i + abbreviation.Length)
                End If
            Next
            returnText = String.Format("{0,3} z-chars + {1} unused slot(s) = {2,3} bytes: {3}{4}{5}",
                                       latestMinimalCost, latestRoundingCost,
                                       (latestMinimalCost + latestRoundingCost) * 2 / 3,
                                       Chr(34), returnText.Replace(SPACE_REPLACEMENT, " ").Replace(LF_REPLACEMENT, "^"), Chr(34))
            Return returnText
        End Function

    End Class
    Public Class PatternData
        Public Key As String = ""
        Public Frequency As Integer = 0
        Public Cost As Integer = 0
        Public Savings As Integer = 0
        Public locked As Boolean = False
        Public Occurrences() As List(Of Integer) = Nothing
        Public lineOfFirstOccurrence As Integer = -1
        Public textLines As HashSet(Of String) = Nothing

        Public ReadOnly Property Score As Integer
            Get
                ' The total savings for the abbreviation
                ' 2 is the cost in zchars for the link to the abbreviation
                ' The abbreviation also need to be stored once and that
                ' requires the cost rounded up the nearest number 
                ' dividable by 3 (3 zhars per word).
                Return (Frequency * (Cost - 2)) - ((Cost + 2) \ 3) * 3
            End Get
        End Property

        Public Function Clone() As PatternData
            Return DirectCast(Me.MemberwiseClone(), PatternData)
        End Function

        Public Sub UpdateOccurrences(gameTextList As List(Of GameText), Optional forceRecalc As Boolean = False)
            If Occurrences Is Nothing Or forceRecalc Then
                ReDim Occurrences(gameTextList.Count)
                For row As Integer = 0 To gameTextList.Count - 1
                    Dim col As Integer = gameTextList(row).text.IndexOf(Me.Key, StringComparison.Ordinal)
                    While col >= 0
                        If Occurrences(row) Is Nothing Then Occurrences(row) = New List(Of Integer)
                        Occurrences(row).Add(col)
                        col = gameTextList(row).text.IndexOf(Me.Key, col + 1, StringComparison.Ordinal)
                    End While
                Next
            End If
        End Sub
    End Class

    Private Function ASCII(cChr As Char) As Byte
        Return TextEncoding.GetBytes(cChr)(0)
    End Function

    Private Function ZstringCost(sText As String) As Integer
        Dim iCost As Integer = 0
        For i As Integer = 0 To sText.Length - 1
            iCost += ZcharCost(sText(i))
        Next
        Return iCost
    End Function

    Private Function ZcharCost(zchar As Char) As Integer
        If alphabet0Hash.Contains(zchar) Then Return 1       ' Alphabet A0 and space
        If alphabet1And2Hash.Contains(zchar) Then Return 2   ' Alphabet A1, A2, quote (") And linefeed 
        Return 4
    End Function

    Private Function RescoreOptimalParse(gameText As List(Of GameText), abbreviations As List(Of PatternData), returnTotalBytes As Boolean, zversion As Integer) As Integer
        ' Parse string using Wagner's optimal parse
        ' https://ecommons.cornell.edu/server/api/core/bitstreams/b2f394c1-f11d-4200-b2d4-1351aa1d12ab/content
        ' https://dl.acm.org/doi/pdf/10.1145/361972.361982

        ' Clear frequency from abbrevs
        For Each abbreviation As PatternData In abbreviations
            abbreviation.Frequency = 0
        Next

        Dim totalBytes As Integer = 0

        ' Iterate over each string and pick optimal set of abbreviations From abbrevs for this string
        For line As Integer = 0 To gameText.Count - 1
            Dim gameTextLine As GameText = gameText(line)
            Dim textLineSB As Text.StringBuilder = gameTextLine.TextSB
            Dim textLine As String = gameTextLine.text
            Dim textLineLength As Integer = textLineSB.Length               ' Cache length

            Dim abbreviationLocations(textLineLength - 1) As List(Of Integer)
            For i As Integer = 0 To abbreviations.Count - 1
                abbreviations(i).UpdateOccurrences(gameText, False)
                Dim lineAbbrevs As List(Of Integer) = abbreviations(i).Occurrences(line)
                If lineAbbrevs IsNot Nothing Then
                    For j As Integer = 0 To lineAbbrevs.Count - 1
                        If abbreviationLocations(lineAbbrevs(j)) Is Nothing Then abbreviationLocations(lineAbbrevs(j)) = New List(Of Integer)
                        abbreviationLocations(lineAbbrevs(j)).Add(i)
                    Next
                End If
            Next

            ' Iterate reverse for optimal parse
            Dim minimalCostFromHere(textLineLength + 1) As Integer ' Wagner's 'f' or 'F'
            Dim pickedAbbreviations(textLineLength) As Integer     ' -1 for "no abbreviation"
            minimalCostFromHere(textLineLength) = 0
            For index As Integer = textLineLength - 1 To 0 Step -1
                Dim charCost As Integer = ZcharCost(textLineSB.Chars(index))
                minimalCostFromHere(index) = minimalCostFromHere(index + 1) + charCost
                pickedAbbreviations(index) = -1
                If abbreviationLocations(index) IsNot Nothing Then
                    For Each abbreviationNumber As Integer In abbreviationLocations(index)
                        Dim abbreviationLength As Integer = abbreviations(abbreviationNumber).Key.Length
                        Dim costWithPattern As Integer = ABBREVIATION_REF_COST + minimalCostFromHere(index + abbreviationLength)
                        If costWithPattern < minimalCostFromHere(index) Then
                            pickedAbbreviations(index) = abbreviationNumber
                            minimalCostFromHere(index) = costWithPattern
                        End If
                    Next
                End If
            Next

            ' Update frequencies from front so only used abbreviations gets updated
            For index As Integer = 0 To textLineLength - 1
                If pickedAbbreviations(index) > -1 Then
                    Dim abbreviationLength As Integer = abbreviations(pickedAbbreviations(index)).Key.Length
                    abbreviations(pickedAbbreviations(index)).Frequency += 1
                    For i As Integer = 1 To abbreviationLength - 1
                        ' Clear overlapped abbreviations
                        pickedAbbreviations(index + i) = -1
                    Next
                    index += abbreviationLength - 1     ' Skip to next slot after abbreviation
                End If
            Next

            ' Aggregate rounding penalty for each string.
            ' zchars are 5 bits and are stored in words (16 bits), 3 in each word. 
            ' Depending on rounding 0, 1 or 2 slots can be "wasted" here.
            Dim roundingNumber = 3
            If gameTextLine.packedAddress Then
                If zversion > 3 Then roundingNumber = 6
                If zversion = 8 Then roundingNumber = 12
            End If
            gameTextLine.latestRoundingCost = (roundingNumber - (minimalCostFromHere(0) Mod roundingNumber)) Mod roundingNumber

            gameTextLine.latestMinimalCost = minimalCostFromHere(0)
            gameTextLine.latestPickedAbbreviations = pickedAbbreviations
            totalBytes += CInt((gameTextLine.latestMinimalCost + gameTextLine.latestRoundingCost) * 2 / 3)
        Next

        Dim totalSavings As Integer = 0
        For Each abbrev As PatternData In abbreviations
            abbrev.Savings = abbrev.Score
            totalSavings += abbrev.Savings
            totalBytes += 2 * ((abbrev.Cost + 2) \ 3)     ' Add cost for storing abbreviations
        Next

        If returnTotalBytes Then
            Return totalBytes
        Else
            Return totalSavings
        End If
    End Function

    Private Function AbbrevSort(abbrevList As List(Of PatternData), sortBottomOfList As Boolean) As List(Of PatternData)
        Dim returnList As New List(Of PatternData)
        For i As Integer = 0 To NumberOfAbbrevs - 1
            returnList.Add(abbrevList(i).Clone)
        Next

        If sortBottomOfList Then
            Dim tmpList As New List(Of PatternData)
            For i As Integer = NumberOfAbbrevs To abbrevList.Count - 1
                If abbrevList(i).Score > 0 Then tmpList.Add(abbrevList(i).Clone)
            Next
            tmpList.Sort(Function(firstPair As PatternData, nextPair As PatternData) CInt(firstPair.Score).CompareTo(CInt(nextPair.Score)))
            tmpList.Reverse()
            For i As Integer = 0 To tmpList.Count - 1
                returnList.Add(tmpList(i).Clone)
            Next
        Else
            returnList.Sort(Function(firstPair As PatternData, nextPair As PatternData) CInt(firstPair.Key.Length).CompareTo(CInt(nextPair.Key.Length)))
            returnList.Reverse()

            For i As Integer = NumberOfAbbrevs To abbrevList.Count - 1
                returnList.Add(abbrevList(i).Clone)
            Next
        End If

        Return returnList
    End Function

    Private Function PrintFormattedAbbreviation(abbreviationNo As Integer, abbreviation As String, frequency As Integer, score As Integer) As String
        Dim padExtra As Integer = 0
        If abbreviationNo < 10 Then padExtra = 1
        Return String.Concat("        .FSTR FSTR?", abbreviationNo.ToString, ",", FormatAbbreviation(abbreviation).PadRight(20 + padExtra), "; ", frequency.ToString.PadLeft(4), "x, saved ", score)
    End Function

    Private Function FormatAbbreviation(abbreviation As String) As String
        Return String.Concat(Chr(34), abbreviation.Replace(SPACE_REPLACEMENT, " ").Replace(QUOTE_REPLACEMENT, String.Concat(Chr(34), Chr(34))).Replace(LF_REPLACEMENT, vbLf), Chr(34))
    End Function

    Private Sub PrintAbbreviations(abbrevList As List(Of PatternData), gameFilename As String, toError As Boolean)
        Dim outStream As IO.TextWriter = Console.Out
        If toError Then outStream = Console.Error

        outStream.WriteLine("        ; Frequent words file for {0}", gameFilename)
        outStream.WriteLine()

        Dim max As Integer = NumberOfAbbrevs - 1
        If abbrevList.Count < max + 1 Then max = abbrevList.Count - 1
        For i As Integer = 0 To max
            outStream.WriteLine(String.Concat(PrintFormattedAbbreviation(i + 1, abbrevList(i).Key, abbrevList(i).Frequency, abbrevList(i).Score)))
        Next

        outStream.WriteLine("WORDS::")

        For i As Integer = 0 To max
            outStream.WriteLine("        FSTR?{0}", i + 1)
        Next

        outStream.WriteLine()
        outStream.WriteLine("        .ENDI")
    End Sub

    Private Sub PrintAbbreviationsI6(abbrevList As List(Of PatternData), toError As Boolean)
        Dim outStream As IO.TextWriter = Console.Out
        If toError Then outStream = Console.Error

        Dim max As Integer = NumberOfAbbrevs - 1
        If abbrevList.Count < max + 1 Then max = abbrevList.Count - 1
        For i As Integer = 0 To max
            Dim line As String = abbrevList(i).Key
            line = line.Replace(SPACE_REPLACEMENT, " ")
            line = line.Replace(LF_REPLACEMENT, "^")
            line = line.Replace("~", QUOTE_REPLACEMENT)
            Dim spaces As Integer = 30 - line.Length
            If spaces < 0 Then spaces = 0
            outStream.WriteLine(String.Concat("Abbreviate ", Chr(34), line, Chr(34), ";", Space(spaces), "! ", abbrevList(i).Frequency.ToString.PadLeft(5), "x, saved ", abbrevList(i).Score.ToString.PadLeft(5)))
        Next
    End Sub

    Private Function IsFileUTF8(fileName As String) As Boolean
        Dim FallbackExp As New System.Text.DecoderExceptionFallback

        Dim fileBytes() As Byte = IO.File.ReadAllBytes(fileName)
        Dim decoderUTF8 = System.Text.Encoding.UTF8.GetDecoder
        decoderUTF8.Fallback = FallbackExp
        Dim IsUTF8 As Boolean
        Try
            Dim charCount As Integer = decoderUTF8.GetCharCount(fileBytes, 0, fileBytes.Length)
            IsUTF8 = True
        Catch
            IsUTF8 = False
        End Try

        Return IsUTF8
    End Function

    Private Function SortAlphabet(alphabetIn As String, AlphabetOrg As String) As String
        Dim alphaArray(AlphabetOrg.Length - 1) As Char
        For i As Integer = 0 To alphaArray.Length - 1
            If alphabetIn.Contains(AlphabetOrg.Substring(i, 1), StringComparison.Ordinal) Then
                alphaArray(i) = CChar(AlphabetOrg.Substring(i, 1))
            Else
                alphaArray(i) = CChar(" ")
            End If
        Next
        For i As Integer = 0 To alphaArray.Length - 1
            If Not New String(alphaArray).Contains(alphabetIn.Substring(i, 1), StringComparison.Ordinal) Then
                For j As Integer = 0 To alphaArray.Length - 1
                    If alphaArray(j) = " " Then
                        alphaArray(j) = CChar(alphabetIn.Substring(i, 1))
                        Exit For
                    End If
                Next
            End If
        Next
        Return New String(alphaArray)
    End Function

    Private Sub PrintAlphabet()
        Console.Out.WriteLine(";" & Chr(34) & "Custom-made alphabet. Insert at beginning of game file." & Chr(34))
        Console.Out.WriteLine("<CHRSET 0 " & Chr(34) & alphabet0 & Chr(34) & ">")
        Console.Out.WriteLine("<CHRSET 1 " & Chr(34) & alphabet1 & Chr(34) & ">")
        ' A2, pos 0 - always escape to 10 bit characters
        ' A2, pos 1 - always newline
        ' A2, pos 2 - insert doublequote (as in Inform6)
        Console.Out.WriteLine("<CHRSET 2 " & Chr(34) & "\" & Chr(34) & alphabet2 & Chr(34) & ">")
        Console.Out.WriteLine()
    End Sub

    Private Sub PrintAlphabetI6()
        Console.Out.WriteLine("! Custom-made alphabet. Insert at beginning of game file (see DM4, §36).")
        Console.Out.WriteLine("Zcharacter")
        Console.Out.WriteLine("    " & Chr(34) & alphabet0.Replace("@", "@{0040}").Replace("\", "@{005C}") & Chr(34))
        Console.Out.WriteLine("    " & Chr(34) & alphabet1.Replace("@", "@{0040}").Replace("\", "@{005C}") & Chr(34))
        ' A2, pos 0 - always escape to 10 bit characters
        ' A2, pos 1 - always newline
        ' A2, pos 2 - always doublequote
        Console.Out.WriteLine("    " & Chr(34) & alphabet2.Replace("@", "@{0040}").Replace("\", "@{005C}") & Chr(34) & ";")
        Console.Out.WriteLine()
    End Sub
End Module

