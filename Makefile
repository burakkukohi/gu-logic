default:
	@latexmk --pdfxe --shell-escape $(tex)

dr:
	@git clean -dfXn

clean:
	@git clean -dfX
