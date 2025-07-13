FROM jupyter/minimal-notebook

RUN pip install --no-cache-dir numpy
RUN pip install --no-cache-dir pandas
RUN pip install --no-cache-dir matplotlib
RUN pip install --no-cache-dir scikit-learn
RUN pip install --no-cache-dir openpyxl
RUN pip install --no-cache-dir seaborn
RUN pip install --no-cache-dir xlrd
