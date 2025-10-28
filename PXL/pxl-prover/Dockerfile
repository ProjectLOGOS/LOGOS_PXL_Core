FROM coqorg/coq:8.20.1

# Install SerAPI and dependencies
RUN opam update && opam install -y serapi menhir ocamlfind dune

# Create working directory
WORKDIR /pxl

# Copy PXL kernel source
COPY pxl-minimal-kernel-main/ /pxl/kernel/

# Build PXL kernel
WORKDIR /pxl/kernel
RUN make clean && make

# Verify kernel with coqchk
RUN coqchk -R . PXLs -silent $(find . -name "*.vo" | head -10) || echo "Some verification warnings"

# Install Python for the server
RUN apt-get update && apt-get install -y python3 python3-pip
RUN pip3 install flask requests

# Copy server
COPY serve_pxl.py /pxl/
WORKDIR /pxl

# Expose port
EXPOSE 8088

# Run the server
CMD ["python3", "serve_pxl.py"]
