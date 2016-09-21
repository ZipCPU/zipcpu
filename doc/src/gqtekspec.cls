%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%/
%
%  Copyright (C) 2015, Gisselquist Technology, LLC
% 
%  This template is free software: you can redistribute it and/or modify it
%  under the terms of the GNU General Public License as published by the
%  Free Software Foundation, either version 3 of the License, or (at your
%  option) any later version.
% 
%  This template is distributed in the hope that it will be useful, but WITHOUT
%  ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
%  FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
%  for more details.
% 
%  You should have received a copy of the GNU General Public License along
%  with this program.  If not, see <http:%%www.gnu.org/licenses/> for a copy.
% 
%  License:	GPL, v3, as defined and found on www.gnu.org,
% 		http://www.gnu.org/licenses/gpl.html
% 
% 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% \NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{gqtekspec}[2015/03/03 v0.1 -- Gisselquist Technology Specification]
\typeout{by Dan Gisselquist}
\LoadClassWithOptions{report}
\usepackage{datetime}
\usepackage{graphicx}
\usepackage[dvips]{pstricks}
\usepackage{hhline}
\usepackage{colortbl}
\definecolor{webgreen}{rgb}{0,0.5,0}
\usepackage[dvips,colorlinks=true,linkcolor=webgreen]{hyperref}
\newdateformat{headerdate}{\THEYEAR/\twodigit{\THEMONTH}/\twodigit{\THEDAY}}
\setlength{\hoffset}{0.25in}
\setlength{\voffset}{-0.5in}
\setlength{\marginparwidth}{0in}
\setlength{\marginparsep}{0in}
\setlength{\textwidth}{6in}
\setlength{\oddsidemargin}{0in}

%    **************************************
%    *         APPENDIX                   *
%    **************************************
%
\newcommand\appfl@g{\appendixname}  %used to test \@chapapp 
%
% \renewcommand\appendix{\par\clearpage
  % \setcounter{chapter}{0}%
  % \setcounter{section}{0}%
  % \renewcommand\@chapapp{\appendixname}%
  % \renewcommand\thechapter{\Alph{chapter}}
  % \if@nosectnum\else
    % \renewcommand\thesection{\Alph{chapter}.\arabic{section}}
  % \fi 
% }


% FIGURE
%   redefine the @caption command to put a period after the figure or 
%   table number in the lof and lot tables
\long\def\@caption#1[#2]#3{\par\addcontentsline{\csname
  ext@#1\endcsname}{#1}{\protect\numberline{\csname
  the#1\endcsname.}{\ignorespaces #2}}\begingroup
    \@parboxrestore
    \normalsize
    \@makecaption{\csname fnum@#1\endcsname}{\ignorespaces #3}\par
  \endgroup}

%    ****************************************
%    *         TABLE OF CONTENTS, ETC.      *
%    ****************************************

\renewcommand\contentsname{Contents}
\renewcommand\listfigurename{Figures}
\renewcommand\listtablename{Tables}

\newif\if@toc \@tocfalse
\renewcommand\tableofcontents{%
    \begingroup% temporarily set if@toc so that \@schapter will not
               % put Table of Contents in the table of contents.
      \@toctrue
      \chapter*{\contentsname}
    \endgroup
    \thispagestyle{gqtekspecplain}
    
    \baselineskip=10pt plus .5pt minus .5pt
    
    {\raggedleft Page \par\vskip-\parskip} 
    \@starttoc{toc}%
    \baselineskip=\normalbaselineskip
  }

\def\l@appendix{\pagebreak[3]
 \vskip 1.0em plus 1pt % space above appendix line
  \@dottedtocline{0}{0em}{8em}}

\def\l@chapter{\pagebreak[3]
 \vskip 1.0em plus 1pt % space above appendix line
  \@dottedtocline{0}{0em}{4em}}

% \if@nosectnum\else
 %  \renewcommand\l@section{\@dottedtocline{1}{5.5em}{2.4em}}
  % \renewcommand\l@subsection{\@dottedtocline{2}{8.5em}{3.2em}}
  % \renewcommand\l@subsubsection{\@dottedtocline{3}{11em}{4.1em}}
  % \renewcommand\l@paragraph{\@dottedtocline{4}{13.5em}{5em}}
  % \renewcommand\l@subparagraph{\@dottedtocline{5}{16em}{6em}}
% \fi
 
% LIST OF FIGURES
%
\def\listoffigures{%
  \begingroup
  \chapter*{\listfigurename}%
  \endgroup
  \thispagestyle{gqtekspecplain}%
  
  \baselineskip=10pt plus .5pt minus .5pt%
  
  {\hbox to \hsize{Figure\hfil Page} \par\vskip-\parskip}%
  
  \rule[2mm]{\textwidth}{0.5mm}\par
  
  \@starttoc{lof}%
  \baselineskip=\normalbaselineskip}%

\def\l@figure{\@dottedtocline{1}{1em}{4.0em}}

% LIST OF TABLES
%
\def\listoftables{%
  \begingroup
  \chapter*{\listtablename}%
  \endgroup
  \thispagestyle{gqtekspecplain}%
  \baselineskip=10pt plus .5pt minus .5pt%
  {\hbox to \hsize{Table\hfil Page} \par\vskip-\parskip}%

  % Added line underneath headings, 20 Jun 01, Capt Todd Hale.
  \rule[2mm]{\textwidth}{0.5mm}\par
  
  \@starttoc{lot}%
  \baselineskip=\normalbaselineskip}%
 
\let\l@table\l@figure

%    ****************************************
%    *            PAGE STYLES               *
%    ****************************************
%
\def\ps@gqtekspectoc{%
      \let\@mkboth\@gobbletwo
      \def \@oddhead{}
      \def \@oddfoot{\rm 
            \hfil\raisebox{-9pt}{\thepage}\hfil\thispagestyle{gqtekspectocn}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}
\def\ps@gqtekspectocn{\let\@mkboth\@gobbletwo
      \def \@oddhead{\rm \hfil\raisebox{10pt}{Page}}
      \def \@oddfoot{\rm 
            \hfil\raisebox{-9pt}{\thepage}\hfil\thispagestyle{gqtekspectocn}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}

\def\ps@gqtekspeclof{\let\@mkboth\@gobbletwo
      \def \@oddhead{}
      \def \@oddfoot{\rm
           \hfil\raisebox{-9pt}{\thepage}\hfil\thispagestyle{gqtekspeclofn}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}
\def\ps@gqtekspeclofn{\let\@mkboth\@gobbletwo
      \def \@oddhead{\rm 
           \parbox{\textwidth}{\raisebox{0pt}{Figure}\hfil\raisebox{0pt}{Page} %
           \raisebox{20pt}{\rule[10pt]{\textwidth}{0.5mm}} }} 
      
      \def \@oddfoot{\rm
           \hfil\raisebox{-9pt}{\thepage}\hfil\thispagestyle{gqtekspeclofn}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}

\def\ps@gqtekspeclot{\let\@mkboth\@gobbletwo
      \def \@oddhead{}
      \def \@oddfoot{\rm
           \hfil\raisebox{-9pt}{\thepage}\hfil\thispagestyle{gqtekspeclotn}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}
\def\ps@gqtekspeclotn{\let\@mkboth\@gobbletwo
      \def \@oddhead{\rm 
           \parbox{\textwidth}{\raisebox{0pt}{Table}\hfil\raisebox{0pt}{Page} %
           \raisebox{20pt}{\rule[10pt]{\textwidth}{0.5mm}} }} 
      
      \def \@oddfoot{\rm
           \hfil\raisebox{-9pt}{\thepage}\hfil\thispagestyle{gqtekspeclotn}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}

\def\ps@gqtekspecplain{\let\@mkboth\@gobbletwo
      \def \@oddhead{\rput(0,-2pt){\psline(0,0)(\textwidth,0)}\rm \hbox to 1in{\includegraphics[height=0.8\headheight]{GT.eps} Gisselquist Technology, LLC}\hfil\hbox{\@title}\hfil\hbox to 1in{\hfil\headerdate\@date}}
      \def \@oddfoot{\rput(0,9pt){\psline(0,0)(\textwidth,0)}\rm \hbox to 1in{www.opencores.com\hfil}\hfil\hbox{\r@vision}\hfil\hbox to 1in{\hfil{\thepage}}}
      \let \@evenhead\@oddhead \let \@evenfoot\@oddfoot}

% \def\author#1{\def\auth@r{#1}}
% \def\title#1{\def\ti@tle{#1}}

\def\logo{\begin{pspicture}(0,0)(5.67in,0.75in)
	\rput[lb](0.05in,0.10in){\includegraphics[height=0.75in]{GT.eps}}
	\rput[lb](1.15in,0.05in){\scalebox{1.8}{\parbox{2.0in}{Gisselquist\\Technology, LLC}}}
	\end{pspicture}}
%  TITLEPAGE
%
\def\titlepage{\setcounter{page}{1}
   \typeout{^^JTitle Page.}
   \thispagestyle{empty}
   \leftline{\rput(0,0){\psline(0,0)(\textwidth,0)}\hfill}
	\vskip 2\baselineskip
	\logo\hfil % Original is 3.91 in x 1.26 in, let's match V thus
	\vskip 2\baselineskip
        \vspace*{10pt}\vfil
	\begin{minipage}{\textwidth}\raggedleft
	\ifproject{\Huge\bfseries\MakeUppercase\@project} \\\fi
	\vspace*{15pt}
	{\Huge\bfseries\MakeUppercase\@title} \\
	\vskip 10\baselineskip
	\Large \@author \\
	\ifemail{\Large \@email}\\\fi
	\vskip 6\baselineskip
	\Large \usdate\@date \\
	\end{minipage}
        % \baselineskip 22.5pt\large\rm\MakeUppercase\ti@tle
        \vspace*{30pt}
	\vfil
        \newpage\baselineskip=\normalbaselineskip}

\newenvironment{license}{\clearpage\typeout{^^JLicense Page.}\ \vfill\noindent}%
	{\vfill\newpage}
%    ****************************************
%    *           CHAPTER DEFINITIONS        *
%    ****************************************
%
\renewcommand\chapter{\if@openright\cleardoublepage\else\clearpage\fi
	\thispagestyle{gqtekspecplain}%
	\global\@topnum\z@
	\@afterindentfalse
	\secdef\@chapter\@schapter}
\renewcommand\@makechapterhead[1]{%
	\hbox  to \textwidth{\hfil{\Huge\bfseries \thechapter.}}\vskip 10\p@
	\hbox to \textwidth{\rput(0,0){\psline[linewidth=0.04in](0,0)(\textwidth,0)}}\vskip \p@
	\hbox to \textwidth{\rput(0,0){\psline[linewidth=0.04in](0,0)(\textwidth,0)}}\vskip 10\p@
	\hbox  to \textwidth{\hfill{\Huge\bfseries #1}}%
	\par\nobreak\vskip 40\p@}
\renewcommand\@makeschapterhead[1]{%
	\hbox  to \textwidth{\hfill{\Huge\bfseries #1}}%
	\par\nobreak\vskip 40\p@}
%    ****************************************
%    *           INITIALIZATION             *
%    ****************************************
%
% Default initializations

\ps@gqtekspecplain          % 'gqtekspecplain' page style with lowered page nos.
\onecolumn             % Single-column.
\pagenumbering{roman}  % the first chapter will change pagenumbering
                       % to arabic
\setcounter{page}{1}   % in case a titlepage is not requested
                       % otherwise titlepage sets page to 1 since the
                       % flyleaf is not counted as a page
\widowpenalty 10000    % completely discourage widow lines
\clubpenalty 10000     % completely discourage club (orphan) lines
\raggedbottom          % don't force alignment of bottom of pages

\date{\today}
\newif\ifproject\projectfalse
\def\project#1{\projecttrue\gdef\@project{#1}}
\def\@project{}
\newif\ifemail\emailfalse
\def\email#1{\emailtrue\gdef\@email{#1}}
\def\@email{}
\def\revision#1{\gdef\r@vision{#1}}
\def\r@vision{}
\def\at{\makeatletter @\makeatother}
\newdateformat{theyear}{\THEYEAR}
\newenvironment{revisionhistory}{\clearpage\typeout{^^JRevision History.}%
	\hbox  to \textwidth{\hfil\scalebox{1.8}{\large\bfseries Revision History}}\vskip 10\p@\noindent%
	\begin{tabular}{|p{0.5in}|p{1in}|p{1in}|p{2.875in}|}\hline
	\rowcolor[gray]{0.8} Rev. & Date & Author & Description\\\hline\hline}
	{\end{tabular}\clearpage}
\newenvironment{clocklist}{\begin{tabular}{|p{0.75in}|p{0.5in}|l|l|p{2.875in}|}\hline
	\rowcolor[gray]{0.85} Name & Source & \multicolumn{2}{l|}{Rates (MHz)} & Description \\\hhline{~|~|-|-|~}%
	\rowcolor[gray]{0.85} & & Max & Min & \\\hline\hline}%
	{\end{tabular}}
\newenvironment{reglist}{\begin{tabular}{|p{0.75in}|p{0.5in}|p{0.5in}|p{0.5in}|p{2.875in}|}\hline
	\rowcolor[gray]{0.85} Name & Address & Width & Access & Description \\\hline\hline}%
	{\end{tabular}}
\newenvironment{bitlist}{\begin{tabular}{|p{0.5in}|p{0.5in}|p{3.875in}|}\hline
	\rowcolor[gray]{0.85} Bit \# & Access & Description \\\hline\hline}%
	{\end{tabular}}
\newenvironment{portlist}{\begin{tabular}{|p{0.75in}|p{0.5in}|p{0.75in}|p{3.375in}|}\hline
	\rowcolor[gray]{0.85} Port & Width & Direction & Description \\\hline\hline}%
	{\end{tabular}}
\newenvironment{wishboneds}{\begin{tabular}{|p{2.5in}|p{2.5in}|}\hline
	\rowcolor[gray]{0.85} Description &  Specification \\\hline\hline}%
	{\end{tabular}}
\newenvironment{preface}{\chapter*{Preface}}{\par\bigskip\bigskip\leftline{\hfill\@author}}
\endinput
