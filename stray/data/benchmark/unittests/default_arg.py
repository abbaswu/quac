import matplotlib.pyplot as plt

def f(x=(5,5)):
    fig = plt.figure(figsize=x)
    ax = fig.add_axes([0, 0, 1, 1], xticks=[], yticks=[], frameon=False)
    # im = ax.imshow(self.state, cmap=plt.cm.binary, interpolation="nearest")
    # im.set_clim(-0.05, 1)
    return fig