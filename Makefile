default:
	@latexmk --pdfxe $(tex)

dr:
	@git clean -dfXn

clean:
	@git clean -dfX
