
manual.pdf: manual.tex manual.bib FigVerifFuncCall.tex
	pdflatex $^
	bibtex manual
	pdflatex $^
	pdflatex $^

clean:
	rm *.aux *.cb *.cb2 *.idx *.lof *.log *.out *.toc *~ manual.pdf
