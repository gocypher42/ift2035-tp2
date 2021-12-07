#!/bin/bash
latexmk -output-directory=../mkrapport -pdf ../rapport.tex 
mv ../mkrapport/rapport.pdf ../
