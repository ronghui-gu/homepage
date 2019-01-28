\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{plt}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{beamer}}
\ProcessOptions
\LoadClass{beamer}

\usefonttheme{professionalfonts}

\setbeamertemplate{navigation symbols}{}

\usepackage[sfdefault]{FiraSans} %% option 'sfdefault' activates Fira Sans as the default text font
\usepackage[T1]{fontenc}
%\renewcommand*\oldstylenums[1]{{\firaoldstyle #1}}
\RequirePackage{frutiger}
\RequirePackage[scaled=0.88]{luximono}

%\RequirePackage{fourier} % Mostly for the math 
%\RequirePackage[T1]{fontenc}

\RequirePackage{listings}
\RequirePackage{booktabs}
\RequirePackage{array}
\RequirePackage[absolute,overlay]{textpos}
\RequirePackage{tikz}
\RequirePackage{calc}

\usetikzlibrary{positioning,%
  shadows,%
  fadings,%
  matrix,%
  fit,%
  backgrounds,%
  calc,%
  shapes.misc,%
  shapes.geometric,%
  shapes.arrows,%
  shapes.callouts,%
  automata,%
  arrows}

\def\partpage{\begin{center}{\Huge\color{blue}\sectionname\par}
  \end{center}
}

\def\part#1{\section{#1}\def\sectionname{#1}}

\graphicspath{{images/}}

\xdefinecolor{Emph}{rgb}{1,0,0}
\xdefinecolor{darkblue}{rgb}{0,0,0.75}
\xdefinecolor{darkgreen}{rgb}{0,0.5,0}
\xdefinecolor{darkred}{rgb}{0.5,0,0}
\xdefinecolor{lightgray}{gray}{0.95}

\tikzset{>=latex} % Nicer looking arrows


\definecolor{mBlue}{HTML}{005580}
\definecolor{mRed}{HTML}{AD003D}

\lstset{
  language=[Objective]caml,
  basicstyle={\fontsize{9}{9.5}\ttfamily\spaceskip=3pt},
  identifierstyle={\itshape},
  keywordstyle=\color{mBlue},       % keyword style
  %keywordstyle={\bfseries},
  commentstyle={\color{darkgreen!60}},
%  columns=fullflexible,
  showstringspaces=false
}

%
% Boxed environment with semi-transparent shadow.
%
\newlength{\boxw}
\newlength{\boxh}
\newlength{\shadowsize}
\newlength{\boxroundness}
\newlength{\tmpa}
\newsavebox{\shadowblockbox}

\setlength{\shadowsize}{6pt}
\setlength{\boxroundness}{3pt}

\newcommand\outputshadowblockbox{
\settowidth{\boxw}{\usebox{\shadowblockbox}}%
\settodepth{\tmpa}{\usebox{\shadowblockbox}}%
\settoheight{\boxh}{\usebox{\shadowblockbox}}%
\addtolength{\boxh}{\tmpa}%
\begin{tikzpicture}
    \addtolength{\boxw}{\boxroundness * 2}
    \addtolength{\boxh}{\boxroundness * 2}

    \foreach \x in {0,.05,...,1}
    {
        \setlength{\tmpa}{\shadowsize * \real{\x}}
        \fill[xshift=\shadowsize - 1pt,yshift=-\shadowsize + 1pt,
                black,opacity=.04,rounded corners=\boxroundness]
            (\tmpa, \tmpa) rectangle +(\boxw - \tmpa - \tmpa,
                \boxh - \tmpa - \tmpa);
    }

    \fill[fill=gray!10, rounded corners=\boxroundness]
        (0, 0) rectangle (\boxw, \boxh);
    \draw node[xshift=\boxroundness,yshift=\boxroundness,
        inner sep=0pt,outer sep=0pt,anchor=south west]
             (0,0) {\usebox{\shadowblockbox}};

\end{tikzpicture}
}

\newcommand{\shadowstart}{\setbox\shadowblockbox\hbox\bgroup}
\newcommand{\shadowend}{\egroup\outputshadowblockbox}

\newenvironment{shadowblock}{\shadowstart}{\shadowend}

\newenvironment{shadedverbatim}{% 
  \topsep=0ex\relax%
  \begin{lrbox}{\shadowblockbox}%
  \begin{minipage}{\textwidth}%
  \fontsize{9}{9.5}\selectfont%
  \begin{semiverbatim}%
}{%
  \end{semiverbatim}%
  \end{minipage}%
  \end{lrbox}%
  \outputshadowblockbox%
}

\newenvironment{interactive}{%
  \begin{lrbox}{\shadowblockbox}%
  \begin{minipage}{\textwidth}%
  \color{red}%
  \newcommand{\type}[1]{\textcolor{black}{##1}}%
  \fontsize{9}{10}\selectfont%
  \newcommand{\li}{\vspace{-0.65\baselineskip}}  
  \begin{semiverbatim}
}
{\end{semiverbatim}%
  \end{minipage}%
  \end{lrbox}%
  \outputshadowblockbox%
}

\parskip=0.5pc


\lstnewenvironment{ocaml}
  {\lstset{language=[Objective]caml}\shadowstart}{\shadowend}

\lstdefinelanguage{ocamllex}{
  morekeywords={open,rule,parse,and,as,eof},
  morestring=[d]',%
  morestring=[b]",%
  morecomment=[n]{(*}{*)},%
  moredelim=**[s][\color{darkblue}]{\{}{\}},%
}

\lstnewenvironment{ocamllex}
  {\lstset{language=ocamllex}\shadowstart}{\shadowend}

\lstdefinelanguage{ocamlyacc}{
  alsoletter=\%,%
  morekeywords={\%token,\%left,\%right,\%nonassoc,\%start,\%type,\%prec,open,\%\%},%
  morecomment=[s]{/*}{*/},%
  moredelim=**[s][\color{darkblue}]{\%\{}{\%\}},
  moredelim=**[s][\color{darkblue}]{\{}{\}},
}

\lstdefinelanguage{assembly}{%
  identifierstyle={\ttfamily},%
  morecomment=[l]{\#},%
}

\lstnewenvironment{ocamlyacc}
  {\lstset{language=ocamlyacc}\shadowstart}{\shadowend}

\lstnewenvironment{C}
  {\lstset{language=C,morekeywords={bool}}\shadowstart}{\shadowend}

\lstnewenvironment{C++}
  {\lstset{language=C++}\shadowstart}{\shadowend}

\lstnewenvironment{assembly}
  {\lstset{language=assembly}\shadowstart}{\shadowend}

\lstnewenvironment{java}
  {\lstset{language=Java}\shadowstart}{\shadowend}

\lstnewenvironment{python}
  {\lstset{language=Python}\shadowstart}{\shadowend}

\lstnewenvironment{cpp}
  {\lstset{language=C++}\shadowstart}{\shadowend}

\lstnewenvironment{basic}
  {\lstset{language=[Visual]Basic}\shadowstart}{\shadowend}

\lstnewenvironment{pascal}
  {\lstset{language=Pascal}\shadowstart}{\shadowend}

\lstnewenvironment{fortran}
  {\lstset{language=FORTRAN}\shadowstart}{\shadowend}

\lstnewenvironment{algol}
  {\lstset{language=[68]algol}\shadowstart}{\shadowend}

\lstnewenvironment{tex}
  {\lstset{language=TeX}\shadowstart}{\shadowend}

\lstnewenvironment{tcl}
  {\lstset{language=tcl}\shadowstart}{\shadowend}

\lstnewenvironment{awk}
  {\lstset{language=awk}\shadowstart}{\shadowend}

\lstnewenvironment{forth}
  {\lstset{morekeywords={CR,ELSE,THEN,IF,BEGIN,NOT,UNTIL}}\shadowstart}{\shadowend}

\lstnewenvironment{lisp}
  {\lstset{language=LISP}\shadowstart}{\shadowend}

\lstnewenvironment{sql}
  {\lstset{language=SQL}\shadowstart}{\shadowend}

\lstnewenvironment{modula}
  {\lstset{language=Modula-2,morekeywords={WHEN}}\shadowstart}{\shadowend}

\lstnewenvironment{prolog}
  {\lstset{language=Prolog}\shadowstart}{\shadowend}

\lstnewenvironment{bash}
  {\lstset{language=sh,morekeywords={local}}\shadowstart}{\shadowend}

\lstnewenvironment{haskell}
  {\lstset{language=Haskell}\shadowstart}{\shadowend}

{\obeyspaces\global\let =\ }
\newenvironment{lcalc}{\begingroup\hfill\shadowstart$\obeyspaces\begin{array}{r@{\;}c@{\;}l}}{\end{array}$\shadowend\hfill\endgroup}

% \begin{twocol}{0.5}
% ...
% \newcol
% ...
% \end{twocol}
\newlength\remainingwidth
\newenvironment{twocol}[1]{\begingroup
\setlength\remainingwidth{\textwidth}
\addtolength\remainingwidth{-#1\textwidth}
\addtolength\remainingwidth{-3pt}
\newcommand{\newcol}{\end{minipage}\begin{minipage}[t]{\remainingwidth}}%
\begin{minipage}[t]{#1\textwidth}}
{\end{minipage}\endgroup}

\newcommand{\frametitlelogo}[3]{
  \frametitle{#1}
  \vbox to 0pt{\vspace{-3pc}\hspace{\textwidth}\llap{\includegraphics[width=#2]{#3}}\vss}
}

% \begin{showscope}
%   foo [    ]
% [          ]
% bar%
% \end{showscope}

\def\mypar{\par\leavevmode}
{\catcode`\^^M=\active % these lines must end with %
  \gdef\myobeylines{\catcode`\^^M\active \let^^M\mypar}}%
\def\obeyampersands{\catcode`\&\active}
{\obeyampersands\global\let&=\&}
\def\obeypounds{\catcode`\#\active}
{\obeypounds\global\let#=\#}
\def\obeyleftbracket{\catcode`[\active}
{\def\startgray#1]{\colorbox{gray}{\color{white}\rule[-\scopedepth]{0pt}{\baselineskip}#1}}
{\obeyleftbracket\global\let[=\startgray}%$
\def\tilde{\char`\~}
\def\obeytildes{\catcode`\~\active\let~=\tilde}
\def\underln{\char`\_}
\def\obeyunderline{\catcode`\_\active}
{\obeyunderline\global\let_=\underln}
\newlength{\scopedepth}
\newenvironment{showscope}{
\shadowstart\vbox\bgroup\parskip=-1pt\fboxsep=0pt\ttfamily%
\setbox 0=\hbox{Ay}%
\setlength{\scopedepth}{\dp0}%
\addtolength{\scopedepth}{2pt}%
\myobeylines\obeyspaces\obeyampersands\obeypounds%
\obeyunderline\obeyleftbracket\obeytildes}{\egroup\shadowend}

\setbeamercolor{popup}{fg=black,bg=mBlue!15}


\newcommand{\hlt}[1]{\textcolor{mRed}{#1}}
% For \url{SOME_URL}, links SOME_URL to the url SOME_URL
\providecommand*\url[1]{\href{#1}{\textcolor{mBlue}{#1}}}
% Same as above, but pretty-prints SOME_URL in teletype fixed-width font
\renewcommand*\url[1]{\href{#1}{\textcolor{mBlue}{#1}}}
% For \email{ADDRESS}, links ADDRESS to the url mailto:ADDRESS
\providecommand*\email[1]{\href{mailto:#1}{\textcolor{mBlue}{#1}}}


