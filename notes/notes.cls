\NeedsTeXFormat{LaTeX2e}[2005/12/01]
\ProvidesClass{notes}[2016/06/23]
\LoadClass{article}

\renewcommand{\@begintheorem}[2]{\trivlist \item[\hskip\labelsep {\sffamily\bfseries #1\ #2:}]}
\renewcommand{\@opargbegintheorem}[3]{\trivlist \item[\hskip\labelsep {\sffamily\bfseries #1\ #2 (#3):}]}

\renewcommand{\maketitle}{{%
    \thispagestyle{first}\raggedright
    \sffamily\let\and\par
    {\huge\bfseries\@title\bigskip\par}
    \Large\@author\bigskip\par
    \normalsize\@date\par
}}

\newcommand{\indicia}{\renewcommand{\@indicia}}
\newcommand{\@indicia}{}

\newcommand{\ps@first}{%
  \def\@evenfoot{\vbox{\footnotesize\sffamily\bigskip\@indicia}}%
  \let\@oddfoot\@evenfoot
  \let\@evenhead\relax
  \let\@oddhead\relax
}
\newcommand{\ps@notes}{%
  \def\@evenhead{\sffamily\footnotesize\@title\hss\thepage}%
  \let\@oddhead\@evenhead
  \let\@evenfoot\relax
  \let\@oddfoot\relax
}
\pagestyle{notes}

\renewcommand{\@seccntformat}[1]{\csname the#1\endcsname. }

\setlength\parindent{1.5em}
\setlength\headheight{3mm}
\setlength\headsep   {10mm}
\setlength\footskip{3mm}
\setlength\textwidth{140mm}
\setlength\textheight{222mm}
\setlength\oddsidemargin{7mm}
\setlength\evensidemargin{15mm}
\setlength\marginparwidth{25mm}
\setlength\topmargin{-12mm}

\renewcommand\section{\@startsection {section}{1}{\z@}%
  {-3.5ex \@plus -1ex \@minus -.2ex}%
  {2.3ex \@plus.2ex}%
  {\sffamily\Large\bfseries\raggedright}}
\renewcommand\subsection{\@startsection{subsection}{2}{\z@}%
  {-3.25ex\@plus -1ex \@minus -.2ex}%
  {1.5ex \@plus .2ex}%
  {\sffamily\large\bfseries\raggedright}}
\renewcommand\subsubsection{\@startsection{subsubsection}{3}{\z@}%
  {-3.25ex\@plus -1ex \@minus -.2ex}%
  {1.5ex \@plus .2ex}%
  {\sffamily\large\bfseries\raggedright}}
\renewcommand\paragraph{\@startsection{paragraph}{4}{\z@}%
  {-3.25ex \@plus-1ex \@minus-.2ex}%
  {1.5ex \@plus .2ex}%
  {\sffamily\normalsize\bfseries\raggedright}}
\renewcommand\subparagraph{\@startsection{subparagraph}{5}{\z@}%
  {3.25ex \@plus1ex \@minus .2ex}%
  {-0.5em}%
  {\sffamily\normalsize\bfseries}}
